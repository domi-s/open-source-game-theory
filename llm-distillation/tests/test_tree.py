"""Lossless program trees and the nearest-library-bot table."""

from __future__ import annotations

import shutil

import pytest

from distillation.canonical import program_key
from distillation.neighbours import edit_distances, nearest, nearest_library_bots
from distillation.resolve import DEFAULT_BOTS_DIR
from distillation.stated import DEFAULT_APP
from distillation.tree import program_tree, tree_size

PRUDENT = "def PrudentBot (k : Nat) : Prog :=\n  .search k (.plays .opp .self Action.C)\n    (.search k (.plays .opp (.bot DefectBot) Action.D)\n      (.const Action.C)\n      (.const Action.D))\n    (.const Action.D)\n"


def tree(source):
    return program_tree(program_key(source))


def test_program_tree_keeps_actions_budgets_and_references():
    assert tree("def B : Prog := .const .C") == ("const", (("action:C", ()),))
    assert tree("def B : Prog := .const .D") != tree("def B : Prog := .const .C")

    t = tree("def B (k : Nat) : Prog := .search (2 * k + 64) (.plays .opp (.bot (CupodBot k)) Action.D) (.const Action.C) (.const Action.D)")
    label, (budget, formula, *_) = t
    assert label == "search" and budget == ("nat:2*k+64", ())
    assert formula == ("plays", (("opp", ()), ("bot", (("ref:CupodBot", (("nat:k", ()),)),)), ("action:D", ())))
    assert tree_size(tree(PRUDENT)) == 19


def test_program_tree_refuses_what_it_cannot_read():
    assert program_tree("") is None
    assert tree("def B : Prog :=\n  let p := .const Action.C\n  .sim p p\n") is None  # layout-sensitive
    assert tree("def B : Prog := .tvote V 1 (.const Action.C) (.const Action.D)") is None
    assert tree("def B : Prog := .const Action.C Action.D") is None  # trailing tokens


def test_nearest_lists_every_tie():
    assert nearest({"A": 3, "B": 1, "C": 1}) == {"nearest": ["B", "C"], "distance": 1}


def test_nearest_library_bots_skips_unparseable_programs_and_bots(tmp_path):
    (tmp_path / "Good.lean").write_text("def Good : Prog := .const Action.C\n", encoding="utf-8")
    (tmp_path / "Letty.lean").write_text("def Letty : Prog :=\n  let p := .self\n  p\n", encoding="utf-8")
    seen = {}

    def fake(app_dir, programs, library):
        seen.update(programs=set(programs), library=set(library))
        return {pid: {name: 0 for name in library} for pid in programs}

    result = nearest_library_bots(None, tmp_path, {"p1": program_key("def X : Prog := .const .D"),
                                                   "p2": program_key("def Y : Prog :=\n  let a := .self\n  a\n"),
                                                   "p3": None}, fake)

    assert seen == {"programs": {"p1"}, "library": {"Good"}}
    assert result == {"p1": {"nearest": ["Good"], "distance": 0}}


@pytest.mark.skipif(shutil.which("uv") is None or not (DEFAULT_APP / "pyproject.toml").exists(),
                    reason="needs uv and the app project (runs the app's tree_edit_distance)")
def test_an_inverted_prudentbot_is_prudentbot_plus_two_edits_in_the_real_app():
    inverted = (PRUDENT.replace("def PrudentBot", "def Inverted")
                .replace("(.plays .opp .self Action.C)", "(.plays .opp .self Action.D)")
                .replace("(.const Action.D)\n", "(.const Action.C)\n"))
    programs = {"inverted": program_key(inverted), "same": program_key(PRUDENT)}

    near = nearest_library_bots(DEFAULT_APP, DEFAULT_BOTS_DIR, programs, edit_distances)

    assert near["same"]["distance"] == 0 and "PrudentBot" in near["same"]["nearest"]
    assert near["inverted"]["distance"] == 2 and "PrudentBot" in near["inverted"]["nearest"]
