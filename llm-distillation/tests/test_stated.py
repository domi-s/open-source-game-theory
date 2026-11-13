"""Stated pipeline: bot extraction and result aggregation (Lean itself is not run)."""

from __future__ import annotations

import json
from pathlib import Path

from distillation.data import load_library
from distillation.stated import _save_results, extract_bot

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
