"""Compile one candidate bot and profile it in Lean. Runs in the APP's environment.

Not imported by the distillation package: ``stated.py`` invokes it as

    uv run --directory <app> python <this file> --name StatedBot3 --opponents A,B,...

with the bot's Lean source on stdin, and reads one JSON object from stdout.

It reuses the app's existing machinery and adds none of its own:
``staged_bot`` places the source where Lean can import it and, on exit, deletes
the source and its build outputs; ``lake env lean`` checks that it compiles
(writes nothing); ``build_profile`` runs the engine's certified evaluator
(``outcomeG``) against each opponent over the budget sweep, with its scratch
files deleted per cell. Nothing is left on disk.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys

from pd_runner.config import load_paths
from pd_runner.services.bot_profile import build_profile, staged_bot


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--name", required=True)
    ap.add_argument("--opponents", required=True, help="comma-separated bot names")
    args = ap.parse_args()
    source = sys.stdin.read()
    engine = load_paths().lean_engine_dir

    with staged_bot(args.name, source) as module:
        path = engine / "PrisonersDilemma" / "Bots" / "LlmGenerations" / f"{args.name}.lean"
        proc = subprocess.run(["lake", "env", "lean", str(path)], cwd=engine,
                              capture_output=True, text=True, timeout=600)
        if proc.returncode != 0:
            print(json.dumps({"valid": False,
                              "error": (proc.stdout + proc.stderr).strip()}))
            return 0
        profile = build_profile(args.name, lean_source=source, module=module,
                                opponents=tuple(args.opponents.split(",")))

    print(json.dumps({"valid": True, "budgets": list(profile.budgets), "cells": [
        {"opponent": c.opponent, "verdict": c.verdict, "my_action": c.my_action,
         "opponent_action": c.opponent_action,
         "by_budget": {str(k): v for k, v in c.by_budget.items()}, "note": c.note}
        for c in profile.cells]}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
