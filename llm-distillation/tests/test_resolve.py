"""Cell resolution: library theorem, else Lean eval, else open (Lean itself is faked)."""

from __future__ import annotations

import json

import pytest

from distillation import stated
from distillation.resolve import (load_library_programs, load_theorems, tag_eval_cell,
                                  theorem_cells)


def theorem(left, right, pair, regime="universal", shared=True):
    return {"left_bot": left, "right_bot": right, "pair": pair, "name": f"outcome_{left}_vs_{right}",
            "budget_regime": regime, "staggered": False,
            "left": f"{left} k" if shared else f"{left} (2 * k + 64)", "right": right}


def test_theorem_cells_read_direct_then_reversed_theorems():
    theorems = {("A", "X"): theorem("A", "X", ["C", "D"]),
                ("Y", "A"): theorem("Y", "A", ["D", "C"]),
                ("A", "N"): theorem("A", "N", ["N", "N"])}  # a proven `none`: no actions
    cells = theorem_cells(["A"], ["X", "Y", "Z", "N"], theorems)

    assert set(cells) == {"X", "Y"}  # Z has no theorem, N has no actions
    assert (cells["X"]["my_action"], cells["X"]["opponent_action"], cells["X"]["swapped"]) == ("C", "D", False)
    # outcome Y A = (D, C)  =>  A plays C against Y, Y plays D, marked for audit
    assert (cells["Y"]["my_action"], cells["Y"]["opponent_action"], cells["Y"]["swapped"]) == ("C", "D", True)
    assert cells["X"]["source"] == "theorem" and cells["X"]["regime"] == "universal"


def test_load_theorems_keeps_only_cells_at_the_shared_budget(tmp_path):
    rows = [theorem("A", "B", ["C", "C"]),
            theorem("A", "C", ["D", "D"], shared=False),                      # B (2 * k + 64)
            dict(theorem("A", "D", ["C", "D"]), staggered=True),               # a companion
            dict(theorem("O", "A", ["C", "D"]), left="O k k")]                 # two params, both k
    path = tmp_path / "t.json"
    path.write_text(json.dumps({"theorems": rows}), encoding="utf-8")

    assert set(load_theorems(path)) == {("A", "B"), ("O", "A")}


def test_library_scan_merges_identical_programs_and_skips_staged_bots(tmp_path):
    body = ".search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D)"
    (tmp_path / "A.lean").write_text(f"namespace PD.Bots\n/-- doc -/\ndef A (k : Nat) : Prog :=\n  {body}\nend PD.Bots\n", encoding="utf-8")
    two = body.replace(" k ", " a ").replace("(.const Action.C) (.const", "(.search b (.plays .opp .self Action.C) (.const Action.C) (.const Action.D)) (.const")
    (tmp_path / "B.lean").write_text(f"def B (a b : Nat) : Prog :=\n  {two}\n", encoding="utf-8")
    (tmp_path / "StatedBot3.lean").write_text(f"def StatedBot3 (k : Nat) : Prog := {body}\n", encoding="utf-8")

    twins = load_library_programs(tmp_path)

    assert sorted(sum(twins.values(), [])) == ["A", "B"]  # the staged copy is not a library bot
    assert len(twins) == 2  # A and B differ (B nests a second search)


def test_the_library_programs_of_the_real_engine_include_prudentbot2_as_prudentbot():
    twins = load_library_programs()
    assert ["PrudentBot", "PrudentBot2"] in twins.values()  # PrudentBot2 k k IS PrudentBot k
    assert not any(n.startswith("StatedBot") for names in twins.values() for n in names)


def _entry(source="def StatedBot0 (k : Nat) : Prog := .const Action.C\n"):
    return {"index": 0, "name": "StatedBot0", "indices": [0], "count": 3, "source": source}


def _worker_result(*cells):
    return {"valid": True, "budgets": [2, 4], "cells": [
        {"opponent": o, "verdict": v, "my_action": a, "opponent_action": "C", "by_budget": {}, "note": ""}
        for o, v, a in cells]}


def test_resolve_entry_runs_lean_only_for_cells_without_a_theorem(monkeypatch):
    asked = {}

    def fake_lean(app_dir, name, source, opponents):
        asked["opponents"] = list(opponents)
        return _worker_result(("Y", "stable", "D"), ("Z", "undetermined", None))

    monkeypatch.setattr(stated, "run_in_lean", fake_lean)
    entry = _entry()
    twins = {stated.program_key(entry["source"]): ["A"]}
    theorems = {("A", "X"): theorem("A", "X", ["C", "D"])}

    stated.resolve_entry(entry, ["X", "Y", "Z"], twins, theorems, None, app_dir=None)

    assert asked["opponents"] == ["Y", "Z"]
    assert entry["valid"] and entry["library_bots"] == ["A"]
    assert [(c["opponent"], c["source"]) for c in entry["cells"]] == [
        ("X", "theorem"), ("Y", "eval"), ("Z", "open")]


def test_resolve_entry_needs_no_lean_when_theorems_cover_every_opponent(monkeypatch):
    monkeypatch.setattr(stated, "run_in_lean", lambda *a: pytest.fail("Lean should not run"))
    entry = _entry()
    twins = {stated.program_key(entry["source"]): ["A"]}
    theorems = {("A", o): theorem("A", o, ["C", "C"]) for o in "XY"}

    stated.resolve_entry(entry, ["X", "Y"], twins, theorems, None, app_dir=None)

    assert entry["valid"] and entry["compiled"] is False
    assert {c["source"] for c in entry["cells"]} == {"theorem"}


def test_resolve_entry_reuses_a_saved_result_and_tags_old_cells(monkeypatch):
    monkeypatch.setattr(stated, "run_in_lean", lambda *a: pytest.fail("Lean should not run"))
    saved = _worker_result(("X", "stable", "C"), ("Y", "phase_dependent", None))  # no `source` yet
    entry = _entry()

    stated.resolve_entry(entry, ["X", "Y"], {}, {}, saved, app_dir=None)

    assert [(c["opponent"], c["source"]) for c in entry["cells"]] == [("X", "eval"), ("Y", "eval")]


def test_a_program_that_does_not_compile_is_invalid(monkeypatch):
    monkeypatch.setattr(stated, "run_in_lean", lambda *a: {"valid": False, "error": "boom"})
    entry = _entry()

    stated.resolve_entry(entry, ["X"], {}, {}, None, app_dir=None)

    assert entry["valid"] is False and entry["error"] == "boom"


def test_tag_eval_cell_marks_only_committed_verdicts_as_eval():
    tag = lambda v: tag_eval_cell({"verdict": v})["source"]
    assert [tag("stable"), tag("phase_dependent"), tag("undetermined")] == ["eval", "eval", "open"]
