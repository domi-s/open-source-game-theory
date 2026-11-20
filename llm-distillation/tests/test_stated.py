"""Stated pipeline: bot extraction and result aggregation (Lean itself is not run)."""

from __future__ import annotations

import json
from pathlib import Path

from distillation.data import load_library
from distillation.classes import group_samples
from distillation.sample import extract_bot
from distillation.stated import _save_results

MATRIX = Path(__file__).resolve().parents[1] / "data" / "payoff_matrix.csv"

DEFINITION = "def MyBot (k : Nat) : Prog := .const Action.C"


def test_extract_bot_renames_and_takes_last_block():
    reply = f"```lean\ndef MyBot := 0\n```\nBetter:\n```lean\n{DEFINITION}\n```"
    assert extract_bot(reply, "StatedBot3") == DEFINITION.replace("MyBot", "StatedBot3") + "\n"


def test_extract_bot_accepts_lean4_fence():
    assert extract_bot(f"```lean4\n{DEFINITION}\n```", "B") is not None


def test_extract_bot_requires_a_block_defining_mybot():
    assert extract_bot("no code here", "B") is None
    assert extract_bot("```lean\ndef Other := 0\n```", "B") is None


def _program(index, definition):
    return {"index": index, "program": definition}


def test_group_samples_merges_identical_programs_and_counts_them():
    other = "def MyBot : Prog := .const Action.D"
    comment = f"/-- same thing -/\n{DEFINITION}"
    classes = group_samples([_program(0, DEFINITION), _program(1, other), _program(2, comment),
                             _program(3, None), _program(4, DEFINITION)])

    assert [(g["index"], g["indices"], g["count"]) for g in classes] == [
        (0, [0, 2, 4], 3), (1, [1], 1), (3, [3], 1)]
    assert classes[0]["name"] == "StatedBot0"
    assert "def StatedBot0 (k : Nat)" in classes[0]["source"]
    assert classes[-1]["source"] is None


def test_weights_equal_profiling_every_sample_separately(tmp_path):
    library = load_library(MATRIX)
    coop = _bot(0, "C", opponents=library.bots)
    defect = _bot(1, "D", opponents=library.bots)
    separate = [coop, dict(coop, index=2), dict(coop, index=3), defect]
    grouped = [dict(coop, count=3), dict(defect, count=1)]

    (tmp_path / "a").mkdir()
    (tmp_path / "b").mkdir()
    _save_results(tmp_path / "a", library, separate, total=4)
    _save_results(tmp_path / "b", library, grouped, total=2)

    def vector(d):
        return json.loads((tmp_path / d / "cooperation_vector.json").read_text(encoding="utf-8"))
    assert vector("a") == vector("b")
    assert vector("b")["x"] == [0.75] * library.n
    assert vector("b")["stable_verdicts"] == [4] * library.n
    report = (tmp_path / "b" / "report.txt").read_text(encoding="utf-8")
    assert "Valid bots: 4/4" in report and "Distinct programs: 2 for 4 samples" in report


def _bot(index, action, verdict="stable", opponents=()):
    cells = [{"opponent": o, "verdict": verdict, "my_action": action} for o in opponents]
    return {"index": index, "name": f"StatedBot{index}", "source": "", "valid": True,
            "cells": cells}


def test_save_results_counts_only_stable_verdicts(tmp_path):
    library = load_library(MATRIX)
    cooperator = _bot(0, "C", opponents=library.bots)
    unsure = _bot(1, "C", verdict="phase_dependent", opponents=library.bots)
    invalid = {"index": 2, "name": "StatedBot2", "source": None, "valid": False}

    _save_results(tmp_path, library, [cooperator, unsure, invalid], total=3)

    vector = json.loads((tmp_path / "cooperation_vector.json").read_text(encoding="utf-8"))
    assert vector["stable_verdicts"] == [1] * library.n
    assert vector["x"] == [1.0] * library.n
    assert "Valid bots: 2/3" in (tmp_path / "report.txt").read_text(encoding="utf-8")


def test_save_results_marks_partial_runs_and_skips_the_fit(tmp_path):
    library = load_library(MATRIX)
    _save_results(tmp_path, library, [_bot(0, "D", verdict="unknown", opponents=library.bots)],
                  total=5)

    report = (tmp_path / "report.txt").read_text(encoding="utf-8")
    assert report.startswith("PARTIAL: 1/5")
    assert "Not fit" in report
    vector = json.loads((tmp_path / "cooperation_vector.json").read_text(encoding="utf-8"))
    assert vector["x"] == [None] * library.n


def _bot_with_one_open_cell(library):
    first, rest = library.bots[0], library.bots[1:]
    bot = _bot(0, "C", opponents=rest)
    bot["cells"].insert(0, {"opponent": first, "verdict": "undetermined", "my_action": None,
                            "note": "timeout", "by_budget": {}})
    bot.update(source="def StatedBot0 (k : Nat) : Prog := .self\n", count=2)
    return first, rest, bot


def test_cells_with_no_proved_answer_are_listed_as_blind_spots(tmp_path):
    library = load_library(MATRIX)
    first, rest, bot = _bot_with_one_open_cell(library)

    _save_results(tmp_path, library, [bot], total=1)

    # the blind spot is listed for the proof pipeline, weighted by its samples
    blind = json.loads((tmp_path / "open_cells.json").read_text(encoding="utf-8"))
    assert [(c["opponent"], c["count"], c["reason"]) for c in blind] == [(first, 2, "timeout")]
    vector = json.loads((tmp_path / "cooperation_vector.json").read_text(encoding="utf-8"))
    assert vector["by_source"][first]["open"] == 2 and vector["by_source"][rest[0]]["eval"] == 2
    assert "OPEN (no theorem, no certified eval): 2" in (tmp_path / "report.txt").read_text(encoding="utf-8")


def test_a_missing_opponent_weakens_the_fit_instead_of_voiding_it(tmp_path):
    library = load_library(MATRIX)
    first, rest, bot = _bot_with_one_open_cell(library)

    _save_results(tmp_path, library, [bot], total=1)

    report = (tmp_path / "report.txt").read_text(encoding="utf-8")
    assert "Not fit" not in report
    assert f"Fit on {len(rest)} of {library.n} opponents. LEFT OUT" in report and first in report
    assert "=== L2 fit ===" in report and "=== BinomialMLE fit ===" in report
    vector = json.loads((tmp_path / "cooperation_vector.json").read_text(encoding="utf-8"))
    assert vector["left_out"] == [first] and vector["x"][0] is None and vector["x"][1:] == [1.0] * len(rest)


def test_nothing_is_fit_when_no_opponent_has_a_proved_answer(tmp_path):
    library = load_library(MATRIX)
    _save_results(tmp_path, library, [_bot(0, "C", verdict="undetermined", opponents=library.bots)],
                  total=1)

    assert "Not fit: no opponent has a proved answer" in (tmp_path / "report.txt").read_text(encoding="utf-8")


def test_the_report_counts_programs_whose_budget_parameters_were_collapsed(tmp_path):
    library = load_library(MATRIX)
    bots = [dict(_bot(0, "C", opponents=library.bots), budget_params=2, count=3),
            dict(_bot(1, "D", opponents=library.bots), budget_params=1)]

    _save_results(tmp_path, library, bots, total=2)

    assert "3 of 4 valid samples had 2+" in (tmp_path / "report.txt").read_text(encoding="utf-8")
