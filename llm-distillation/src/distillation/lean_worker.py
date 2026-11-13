"""Compile one candidate bot and profile it in Lean. Runs in the APP's environment.

Not imported by the distillation package: ``stated.py`` invokes it as

    uv run --directory <app> python <this file> --name StatedBot3 --opponents A,B,...

with the bot's Lean source on stdin, and reads one JSON object from stdout.

It reuses the app's machinery: ``staged_bot`` places the source where Lean can
import it and, on exit, deletes the source and its build outputs; ``lake build``
of that module is the validity check; the cells are the app's certified
evaluator (``outcomeG (guardFastN k) 64``, sound by ``outcomeG_sound``), and the
budget ladder is collapsed by the app's own ``_classify``.

The one difference from ``build_profile``: all cells run in ONE Lean process.
Importing the engine costs ~1 min here, so ``build_profile``'s process per cell
(36 per bot) spends nearly all its time importing and times most cells out. Lean
prints ``#eval`` output only at exit when piped, so each cell instead appends its
result to a file, which we poll to keep a per-cell timeout: a cell that hangs is
recorded as a timeout and Lean is restarted on the cells after it.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from pd_runner.config import load_paths
from pd_runner.eval.outcome_prepass import (
    _DECIDER_MODULE, _OOM_RE, REGISTRY, CellResult, bot_spec_from_source)
from pd_runner.services.bot_profile import (
    DEFAULT_BUDGETS, PROFILE_MEMORY_MB, _classify, staged_bot)

FUEL = 64              # run_cells' default evaluator fuel
CELL_TIMEOUT = 120     # seconds per cell once the imports are loaded
IMPORT_TIMEOUT = 600   # extra allowance for the first cell of each Lean process
_LINE_RE = re.compile(r"^(\d+) (.*)$")


def _batch_source(imports, cells, out: Path) -> str:
    lines = [f"import {m}" for m in sorted(imports)]
    lines += ["open PD PD.Bots PD.T31", "",
              "def pdOut (i : Nat) (r : Option Outcome) : IO Unit := do",
              f'  let h ← IO.FS.Handle.mk "{out.as_posix()}" .append',
              '  h.putStrLn s!"{i} {repr r}"',
              "  h.flush", ""]
    for i, _, left, right, k in cells:
        lines.append(f"#eval pdOut {i} (outcomeG (guardFastN {k}) {FUEL} ({left}) ({right}))")
    return "\n".join(lines) + "\n"


def _run_batch(engine: Path, imports, cells, done: dict) -> None:
    """Evaluate ``cells`` (list of (index, ...)) into ``done``; restart past hangs."""
    pending = list(cells)
    while pending:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "results.txt"
            out.touch()
            src = Path(tmp) / "batch.lean"
            src.write_text(_batch_source(imports, pending, out), encoding="utf-8")
            proc = subprocess.Popen(
                ["lake", "env", "lean", "-M", str(PROFILE_MEMORY_MB), str(src)],
                cwd=engine, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                encoding="utf-8", errors="replace")
            started = time.monotonic()
            deadline = started + IMPORT_TIMEOUT + CELL_TIMEOUT
            seen = 0
            while True:
                exited = proc.poll() is not None
                lines = out.read_text(encoding="utf-8").splitlines()
                if len(lines) > seen:
                    now = time.monotonic()
                    for line in lines[seen:]:
                        m = _LINE_RE.match(line)
                        if m:
                            done[int(m.group(1))] = (m.group(2), now - started)
                    seen = len(lines)
                    started = now
                    deadline = now + CELL_TIMEOUT
                if exited or time.monotonic() > deadline:
                    break
                time.sleep(1)
            timed_out = not exited
            if timed_out:
                proc.kill()
            log = proc.communicate()[0] or ""
        rest = [c for c in pending if c[0] not in done]
        if not rest:
            return
        # The first unfinished cell is the one that hung or crashed Lean.
        i = rest[0][0]
        if timed_out:
            done[i] = ("timeout", None)
        elif _OOM_RE.search(log):
            done[i] = ("oom", None)
        else:
            done[i] = ("error: " + log.strip()[-300:], None)
        pending = rest[1:]


def _cell_result(bot, opp, k, raw) -> CellResult:
    value, seconds = raw
    if value.startswith("some ("):
        acts = re.findall(r"Action\.([CD])", value)
        return CellResult(bot, opp, k, k, FUEL, "determined", f"({acts[0]}, {acts[1]})",
                          "certified: outcomeG_sound ∘ guardFastN_sound", seconds or 0.0)
    if value == "none":
        return CellResult(bot, opp, k, k, FUEL, "undetermined", None,
                          f"Löb boundary or budget floor at k={k}", seconds or 0.0)
    if value == "timeout":
        return CellResult(bot, opp, k, k, FUEL, "timeout", None,
                          f"no verdict within {CELL_TIMEOUT}s", 0.0)
    if value == "oom":
        return CellResult(bot, opp, k, k, FUEL, "oom", None,
                          f"exceeded {PROFILE_MEMORY_MB}MB cap", 0.0)
    return CellResult(bot, opp, k, k, FUEL, "error", None, value, 0.0)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--name", required=True)
    ap.add_argument("--opponents", required=True, help="comma-separated bot names")
    args = ap.parse_args()
    source = sys.stdin.read()
    engine = load_paths().lean_engine_dir
    opponents = args.opponents.split(",")

    with staged_bot(args.name, source) as module:
        # Compile straight to the .olean the batch imports (and staged_bot deletes).
        # Not `lake build`: even a no-op one re-hashes ~3100 modules (~70s here).
        # The opponents and the decider must already be built (`lake build` once,
        # plus `lake build +PrisonersDilemma.Decidability.T31Sound`).
        rel = Path(*module.split("."))
        lib = engine / ".lake" / "build" / "lib" / "lean"
        (lib / rel).parent.mkdir(parents=True, exist_ok=True)
        proc = subprocess.run(
            ["lake", "env", "lean", str(engine / rel.with_suffix(".lean")),
             "-o", str(lib / rel.with_suffix(".olean")),
             "-i", str(lib / rel.with_suffix(".ilean"))],
            cwd=engine, capture_output=True, encoding="utf-8", errors="replace",
            timeout=1800)
        if proc.returncode != 0:
            print(json.dumps({"valid": False,
                              "error": (proc.stdout + proc.stderr).strip()[-4000:]}))
            return 0
        spec = bot_spec_from_source(args.name, module, source)
        specs = [REGISTRY[o] for o in opponents]
        imports = {module, _DECIDER_MODULE, *(s.module for s in specs)}

        cells, skipped = [], {}
        for o, s in zip(opponents, specs):
            for k in DEFAULT_BUDGETS:
                i = len(cells) + len(skipped)
                if spec.guard is not None and s.guard is not None and k > 2:
                    skipped[i] = (o, k)  # same rule as run_cells: infeasible in calibration
                    continue
                cells.append((i, o, spec.expr.format(k=k), s.expr.format(k=k), k))
        done: dict[int, tuple] = {}
        if cells:  # cheapest budgets first, so a hang costs the fewest cells
            _run_batch(engine, imports, sorted(cells, key=lambda c: c[4]), done)

    results = {o: [] for o in opponents}
    for i, o, _, _, k in cells:
        results[o].append(_cell_result(args.name, o, k, done[i]))
    for i, (o, k) in skipped.items():
        results[o].append(CellResult(args.name, o, k, k, FUEL, "skipped", None,
                                     "both-searcher cell at k>2", 0.0))
    profile = [_classify(o, results[o]) for o in opponents]

    print(json.dumps({"valid": True, "budgets": list(DEFAULT_BUDGETS), "cells": [
        {"opponent": c.opponent, "verdict": c.verdict, "my_action": c.my_action,
         "opponent_action": c.opponent_action,
         "by_budget": {str(k): v for k, v in c.by_budget.items()}, "note": c.note}
        for c in profile]}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
