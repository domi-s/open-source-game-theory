"""Canonical form of stated bots: what must merge, and what must NOT."""

from __future__ import annotations

from distillation.canonical import budget_params, canonicalise, program_key, strip_comments

TWO_TIER = """\
import PrisonersDilemma.Program
import PrisonersDilemma.Bots.DefectBot

open PD
namespace PD.Bots

/-- MyBot: two-tier PrudentBot.
    /- nested -/ still a comment -/
def MyBot ({outer} {inner} : Nat) : Prog :=
  .search {outer} (.plays .opp .self Action.C)
    (.search {inner} (.plays .opp (.bot DefectBot) Action.D)
      (.const Action.C)
      (.const Action.D))
    (.const Action.D)  -- else: defect

end PD.Bots
"""


def two_tier(outer="kOut", inner="kIn"):
    return TWO_TIER.format(outer=outer, inner=inner)


def test_comments_name_and_budget_names_are_erased():
    a = canonicalise(two_tier("kOut", "kIn"))
    assert a == canonicalise(two_tier("a", "b").replace("MyBot", "Other"))
    assert "--" not in a and "/-" not in a
    assert "def StatedBot (k : Nat) : Prog := .search k " in a


def test_budget_order_is_order_of_first_use_in_the_body():
    # Declared (inner outer) but used outer-first: same program as (outer inner).
    swapped = two_tier("kOut", "kIn").replace("(kOut kIn : Nat)", "(kIn kOut : Nat)")
    assert canonicalise(swapped) == canonicalise(two_tier("kOut", "kIn"))


def test_grouped_and_separate_binders_agree():
    grouped = two_tier()
    separate = grouped.replace("(kOut kIn : Nat)", "(kOut : Nat) (kIn : Nat)")
    assert canonicalise(grouped) == canonicalise(separate)


def test_layout_and_import_order_do_not_matter():
    a = two_tier()
    b = a.replace("\n    (.search", " (.search").replace(
        "import PrisonersDilemma.Program\nimport PrisonersDilemma.Bots.DefectBot",
        "import PrisonersDilemma.Bots.DefectBot\nimport PrisonersDilemma.Program")
    assert b != a
    assert canonicalise(a) == canonicalise(b)


def test_the_name_argument_names_the_bot():
    assert "def StatedBot7 (k : Nat)" in canonicalise(two_tier(), "StatedBot7")
    assert canonicalise(canonicalise(two_tier(), "StatedBot7")) == canonicalise(two_tier())


def test_different_programs_stay_different():
    base = canonicalise(two_tier())
    flipped = two_tier().replace("Action.D))\n    (.const Action.D)",
                                 "Action.D))\n    (.const Action.C)")
    assert flipped != two_tier()
    assert canonicalise(flipped) != base
    # a budget EXPRESSION in the body is the program's own, not a parameter: kept
    staggered = two_tier().replace("(.search kIn", "(.search (2 * kOut + 64)")
    assert staggered != two_tier()
    assert canonicalise(staggered) != base


def test_every_budget_parameter_is_the_one_shared_k():
    # PrudentBot2 k k IS PrudentBot k: two parameters collapse to one `k`...
    two = two_tier("kOut", "kIn")
    one = two_tier("k", "k").replace("(k k : Nat)", "(k : Nat)")
    assert canonicalise(two) == canonicalise(one)
    # ...also with an unused spare parameter
    spare = two.replace("(kOut kIn : Nat)", "(kOut kIn spare : Nat)")
    assert canonicalise(spare) == canonicalise(one)
    assert budget_params(two) == 2 and budget_params(one) == 1
    assert budget_params("def B : Prog := .const Action.C") == 0


def test_a_k_that_is_not_a_parameter_blocks_the_collapse():
    src = ("def B (j : Nat) : Prog :=\n  let k := j\n"
           "  .search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D)\n")
    assert "def StatedBot (j : Nat)" in canonicalise(src)


def test_action_shorthand_is_the_same_program_but_c_is_not_d():
    assert canonicalise("def B : Prog := .const .C") == canonicalise("def B : Prog := .const Action.C")
    assert canonicalise("def B : Prog := .const .C") != canonicalise("def B : Prog := .const .D")
    # `.DefectBot` is not an action
    assert canonicalise("def B : Prog := .bot .DefectBot") == "def StatedBot : Prog := .bot .DefectBot\n"


def test_qualified_constructors_are_the_dot_form():
    dot = "def B (k : Nat) : Prog := .search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D)"
    qual = ("def B (k : Nat) : Prog := Prog.search k (Formula.plays Prog.opp PD.Prog.self Action.C) "
            "(Prog.const Action.C) (Prog.const Action.D)")
    assert canonicalise(qual) == canonicalise(dot)
    assert "Prog.size" in canonicalise("def B : Prog := .const (if Prog.size .self = 0 then .C else .D)")


def test_spacing_around_arithmetic_does_not_matter():
    assert (canonicalise("def B (k : Nat) : Prog := .search (2*k+64) (.box k (.neg (.plays .opp .self .C))) (.const .C) (.const .D)")
            == canonicalise("def B (k : Nat) : Prog := .search (2 * k + 64) (.box k (.neg (.plays .opp .self .C))) (.const .C) (.const .D)"))


def test_program_key_is_one_named_def_whatever_surrounds_it():
    file = ("import X\nnamespace PD.Bots\ndef Helper : Prog := .const .C\n"
            "/-- doc -/\ndef Target (a b : Nat) : Prog :=\n  .const .D\n\nend PD.Bots\n")
    assert program_key(file, "Target") == "def StatedBot (k : Nat) : Prog := .const Action.D\n"
    assert program_key(file) == "def StatedBot : Prog := .const Action.C\n"
    assert program_key(file, "Missing") is None


def test_layout_sensitive_bodies_keep_their_newlines():
    src = "def B : Prog :=\n  let p := .const Action.C\n  .sim p p\n"
    out = canonicalise(src)
    assert "let p := .const Action.C\n" in out  # joining would parse `.const Action.C .sim p p`


def test_strip_comments_respects_strings_and_nesting():
    assert strip_comments('a /- x /- y -/ z -/ b -- tail\nc') == "a   b \nc"
    assert strip_comments('s := "--not a comment"') == 's := "--not a comment"'
