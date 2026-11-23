"""Command-line entry point: compare a model's stated programs to how it plays.

Usage::

    distillation-fidelity --stated runs/<stated run> --revealed runs/<revealed run>

Both runs must be of the same model. Needs no API key and no Lean: it reads saved runs.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from .fidelity import check_same_model, compare, format_report, load_revealed, load_stated

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="distillation-fidelity",
        description="Compare the programs an LLM states with how it plays, per opponent.")
    parser.add_argument("--stated", type=Path, required=True,
                        help="A distillation-stated run folder (needs bots.json).")
    parser.add_argument("--revealed", type=Path, required=True,
                        help="A distillation-llm run folder (needs raw_responses.json).")
    parser.add_argument("--delta", type=float, default=0.05,
                        help="Failure probability of the confidence interval. Default: 0.05.")
    args = parser.parse_args(argv)
    try:
        model = check_same_model(args.stated, args.revealed)
        result = compare(load_stated(args.stated), load_revealed(args.revealed), args.delta)
    except (ValueError, FileNotFoundError) as error:
        parser.error(str(error))
    print(format_report(model, result))
    return 0

if __name__ == "__main__":
    sys.exit(main())
