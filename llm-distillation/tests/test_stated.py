"""Approach 3 (stated strategy): parser, evaluator, aggregation, pipeline."""

from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

import numpy as np
import pytest

from distillation.data import load_library
from distillation.stated.aggregate import aggregate, build_report, type_distribution
from distillation.stated.evaluate import (
    NONTERMINATING, Evaluator, MatrixOracle, Undetermined, profile,
)
from distillation.stated.parse import ParseError, extract_lean, judge, parse_file
from distillation.stated.pipeline import StatedConfig, analyse, run_stated
from distillation.stated.prog import Bot, Eq, Search, budgets
from distillation.stated.zoo import instance, zoo_scope

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
MATRIX = ROOT / "data" / "payoff_matrix.csv"
EXPORT = REPO / "app" / "generated" / "outcome_theorems.json"
ENGINE_BOTS = REPO / "engine" / "PrisonersDilemma" / "Bots"


@pytest.fixture(scope="module")
def library():
    return load_library(MATRIX)


@pytest.fixture(scope="module")
def oracle(library):
    return MatrixOracle.from_library(library.bots, library.R)


def lean_block(body: str) -> str:
    return f"Here is my bot.\n```lean\n{body}\n```\n"


# ----------------------------------------------------------------------- parser
def test_zoo_snapshot_matches_engine_sources():
    """The embedded zoo must parse to the same ASTs as the engine's own files."""
    if not ENGINE_BOTS.is_dir():
        pytest.skip("engine checkout not present")
    files = sorted(ENGINE_BOTS.glob("*.lean")) + sorted(ENGINE_BOTS.glob("LlmGenerations/*.lean"))
    checked = 0
    for f in files:
        parsed = parse_file(f.read_text(), zoo_scope())
        for name, d in parsed.defs.items():
            assert name in zoo_scope(), f"{name} ({f.name}) missing from the snapshot"
            assert d.params == zoo_scope()[name].params, name
            assert d.body == zoo_scope()[name].body, f"{name} drifted from {f.name}"
            checked += 1
    assert checked >= 18


def test_parser_accepts_qualified_names_helpers_and_lets():
    src = """
    import PrisonersDilemma.Program
    open PD
    namespace PD.Bots
    /-- a helper -/
    def Helper (j : Nat) : Prog := .search j (.plays .opp .self Action.C) (.const .C) (.const .D)
    def MyBot (k : Nat) : Prog :=
      let probe : Prog := .sim .opp (.bot PD.Bots.CooperateBot)   -- comment
      .ite probe Action.C (Helper k) (Prog.const Action.D)
    end PD.Bots
    """
    parsed = parse_file(src, zoo_scope())
    body = parsed.defs["MyBot"].body
    assert parsed.order == ["Helper", "MyBot"]
    assert body.then == Search("k", instance("DupocBot").formula,
                               instance("DupocBot").then, instance("DupocBot").els)
    assert budgets(body) == {"k"}


def test_budget_arguments_are_substituted():
    d = parse_file("def MyBot (a b : Nat) : Prog := .bot (PrudentBot2 a (2 * b + 1))",
                   zoo_scope()).defs["MyBot"]
    assert budgets(d.body) == {"a", "2 * b + 1"}


@pytest.mark.parametrize("src, msg", [
    ("def MyBot (k : Nat) : Prog := .search k (.diag k (.plays .opp .self .C)) (.const .C) (.const .D)",
     "outside the supported fragment"),
    ("def MyBot : Prog := .tvote .nil 0 (.const .C) (.const .D)", "outside the supported fragment"),
    ("def MyBot : Prog := NotABot", "unknown name"),
    ("def MyBot (k : Nat) : Prog := .search k (.plays .opp .self .C) (.const .C)",
     "unexpected end"),
    ("def MyBot (x : Bool) : Prog := .const .C", r"only \(x : Nat\)"),
])
def test_parser_rejects(src, msg):
    with pytest.raises(ParseError, match=msg):
        parse_file(src, zoo_scope())


def test_extract_takes_the_last_lean_block():
    text = "```lean\ndef MyBot : Prog := .const .D\n```\nActually:\n```lean\ndef MyBot : Prog := .const .C\n```"
    assert ".const .C" in extract_lean(text)
    assert extract_lean("no code here") is None


def test_judge_lints():
    hard = judge(0, lean_block("def MyBot (k : Nat) : Prog := .search 1000 (.plays .opp .self .C) (.const .C) (.const .D)"), zoo_scope())
    assert not hard.valid and "hard-coded budget" in hard.errors[0]
    unwrapped = judge(1, lean_block("def MyBot : Prog := .sim .opp MirrorBot"), zoo_scope())
    assert unwrapped.valid and any("not wrapped in .bot" in w for w in unwrapped.warnings)
    renamed = judge(2, lean_block("def Other : Prog := .const .C"), zoo_scope())
    assert renamed.valid and renamed.name == "Other"


# -------------------------------------------------------------------- evaluator
def test_evaluator_agrees_with_every_kernel_cell_it_decides(oracle):
    """The evaluator's own rules never contradict Lean.

    Cells resolved through a matrix frame are skipped: they are only as good as
    the reference matrix, which is not what this test is about.
    """
    if not EXPORT.is_file():
        pytest.skip("outcome export not present")
    lean = {}
    for t in json.loads(EXPORT.read_text())["theorems"]:
        if t["staggered"]:
            continue
        a, b = t["pair"] or (NONTERMINATING, NONTERMINATING)
        lean[(t["left_bot"], t["right_bot"])] = a
        lean[(t["right_bot"], t["left_bot"])] = b
    decided = 0
    for (a, b), want in lean.items():
        if a not in zoo_scope() or b not in zoo_scope() or len(zoo_scope()[a].params) > 1 \
                or len(zoo_scope()[b].params) > 1:
            continue
        ev = Evaluator(oracle)
        try:
            got = ev.play(instance(a), instance(b))
        except Undetermined:
            continue
        if "matrix-frame" in ev.flags:
            continue
        assert got == want, f"{a} vs {b}: evaluator {got}, kernel {want}"
        decided += 1
    assert decided >= 50


def test_search_free_cells_are_computed_not_looked_up(oracle):
    ev = Evaluator(oracle)
    # search-free pair: derived by evaluation, no matrix lookup
    assert ev.play(instance("EBot"), instance("TitForTatBot")) == "C"
    assert ev.play(instance("TitForTatBot"), instance("EBot")) == "D"
    assert "matrix-frame" not in ev.flags


def test_mirror_self_play_is_detected_as_a_loop(oracle):
    assert Evaluator(oracle).play(instance("MirrorBot"), instance("MirrorBot")) == NONTERMINATING


def test_eq_guard_is_syntactic_and_sees_the_bot_wrapper(oracle):
    troll = instance("CupodTrollBot")
    ev = Evaluator(oracle)
    assert ev.play(troll, instance("CupodBot")) == "D"
    # a probe sees `.bot CupodBot`, which is NOT literally CupodBot (spec §4.3)
    assert ev.play(troll, Bot(instance("CupodBot"))) == "C"


def test_lob_cooperation_is_undetermined_but_zoo_identity_reads_the_row(oracle, library):
    # off-library (different budget symbol): Löb is beyond the evaluator
    with pytest.raises(Undetermined):
        Evaluator(oracle).play(instance("DupocBot", "j"), instance("DupocBot", "j"))
    # both players ARE library bots: the frame falls back to the matrix, flagged
    ev = Evaluator(oracle)
    assert ev.play(instance("DupocBot"), instance("DupocBot")) == "C"
    assert "matrix-frame" in ev.flags
    d = zoo_scope()["DupocBot"]
    cells = profile(d.body, d.params, oracle)
    i = library.bots.index("DupocBot")
    assert [cells[b].value for b in library.bots] == \
        ["C" if v else "D" for v in library.R[i]]
    assert all(c.provenance == ("zoo-identity",) for c in cells.values())


def test_same_k_convention_maps_two_tier_bots_onto_one_budget(oracle):
    d = zoo_scope()["PrudentBot2"]
    from distillation.stated.evaluate import same_k
    assert same_k(d.body, d.params) == instance("PrudentBot")


# ------------------------------------------------------------------ aggregation
def _judged(library, oracle, bodies):
    samples = [judge(i, lean_block(b), zoo_scope()) for i, b in enumerate(bodies)]
    profiles = {s.index: profile(s.program, s.params, oracle) for s in samples if s.valid}
    return samples, profiles


def test_average_then_fit_and_fit_then_average_recover_zoo_frequencies(library, oracle):
    bodies = ["def MyBot : Prog := " + src for src in [
        ".ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.const Action.D)",
        ".ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.const Action.D)",
        ".const Action.D",
        ".const Action.C",
    ]] + ["def MyBot : Prog := .search 7 (.plays .opp .self .C) (.const .C) (.const .D)"]  # invalid
    samples, profiles = _judged(library, oracle, bodies)
    agg = aggregate(library, samples, profiles)
    assert (agg.n_valid, agg.n_total) == (4, 5)
    assert agg.covered.all()

    want = np.zeros(library.n)
    for name, f in [("TitForTatBot", 0.5), ("DefectBot", 0.25), ("CooperateBot", 0.25)]:
        want[library.bots.index(name)] = f
    np.testing.assert_allclose(agg.x, library.R.T @ want)

    wbar, used = type_distribution(library, samples, profiles, agg.covered)
    assert used == 4
    np.testing.assert_allclose(library.R.T @ wbar, agg.x, atol=1e-6)

    report, _ = build_report(library, samples, profiles,
                             revealed={b: 0.5 for b in library.bots})
    assert "valid programs: 4/5" in report
    assert "[syntactically TitForTatBot]" in report
    assert "Stated (written programs) vs revealed" in report


def test_undetermined_cells_are_missing_not_defections(library, oracle):
    # a self-referential guard over a non-zoo program: Löb, undetermined vs searchers
    samples, profiles = _judged(library, oracle, [
        "def MyBot (k : Nat) : Prog := .search k (.plays .opp .self .C) (.const .C) (.ite (.const .C) .C (.const .D) (.const .D))"])
    agg = aggregate(library, samples, profiles)
    assert agg.undetermined.sum() > 0
    assert np.all(agg.c + (agg.n - agg.c) + agg.undetermined + agg.nonterminating == 1)
    j = library.bots.index("DefectBot")
    assert agg.n[j] == 1 and agg.c[j] == 0  # vs DefectBot it is decidable: D


# ---------------------------------------------------------------------- pipeline
class FakeClient:
    def __init__(self, replies):
        self.replies = list(replies)
        self.chat = SimpleNamespace(completions=SimpleNamespace(create=self._create))

    def _create(self, **kwargs):
        text = self.replies.pop(0)
        if isinstance(text, Exception):
            raise text
        return SimpleNamespace(choices=[SimpleNamespace(message=SimpleNamespace(content=text))])


def test_pipeline_writes_a_complete_run_and_reanalyzes(tmp_path):
    spec = tmp_path / "spec.md"
    spec.write_text("# spec stub")
    replies = [
        lean_block("def MyBot : Prog := .bot TitForTatBot"),
        lean_block("def MyBot (k : Nat) : Prog := DupocBot k"),
        "I refuse to write code.",
        RuntimeError("rate limited"),
    ]
    config = StatedConfig(model="test/model", n=4, matrix_path=MATRIX,
                          output_root=tmp_path, spec_path=spec)
    run_dir = run_stated(config, client=FakeClient(replies))

    for f in ("metadata.json", "prompt.txt", "raw_responses.json", "programs.json",
              "stated_vector.json", "report.txt"):
        assert (run_dir / f).is_file(), f
    meta = json.loads((run_dir / "metadata.json").read_text())
    assert meta["mode"] == "stated" and meta["n"] == 4
    assert "# spec stub" in (run_dir / "prompt.txt").read_text()

    programs = json.loads((run_dir / "programs.json").read_text())
    assert [p["valid"] for p in programs] == [True, True, False, False]
    assert programs[3]["errors"][0].startswith("api error")
    assert programs[1]["profile"]["DefectBot"]["provenance"] == ["zoo-identity"]

    vec = json.loads((run_dir / "stated_vector.json").read_text())
    assert vec["valid_programs"] == 2 and set(vec["by_bot"]) == set(load_library(MATRIX).bots)

    before = (run_dir / "report.txt").read_text()
    assert analyse(run_dir, MATRIX) == before
