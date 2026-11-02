"""``distillation-stated``: approach 3 -- ask the LLM to WRITE its strategy as Prog.

    distillation-stated --model anthropic/claude-sonnet-4.5 --n 30
    distillation-stated --model openai/gpt-4o --show-zoo --revealed runs/<revealed-run>
    distillation-stated --reanalyze runs/<stated-run>      # no API calls

Requires ``OPENROUTER_API_KEY`` unless ``--reanalyze`` is used.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from .pipeline import StatedConfig, analyse, run_stated
from .prompt import DEFAULT_SPEC_PATH


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="distillation-stated",
        description="Sample Prog programs in which an LLM states its own strategy, "
        "profile each against the library, and fit the averaged profile.")
    p.add_argument("--model", help="OpenRouter model id (required unless --reanalyze).")
    p.add_argument("--n", type=int, default=30, help="Programs to sample. Default: 30.")
    p.add_argument("--temperature", type=float, default=1.0,
                   help="Sampling temperature (>0, or every sample is the same). "
                   "Default: 1.0.")
    p.add_argument("--matrix", type=Path, default=Path("data/payoff_matrix.csv"),
                   help="Reference matrix CSV (fits AND the evaluator's matrix frames).")
    p.add_argument("--output-root", type=Path, default=Path("runs"))
    p.add_argument("--spec", type=Path, default=DEFAULT_SPEC_PATH,
                   help="The Prog language spec embedded in the prompt.")
    p.add_argument("--show-zoo", action="store_true",
                   help="Also show the library bots' pseudocode in the prompt "
                   "(an experimental condition: the model may tailor to the zoo).")
    p.add_argument("--fuel", type=int, default=300,
                   help="Evaluator recursion depth per play. Default: 300.")
    p.add_argument("--revealed", type=Path,
                   help="A revealed-strategy run folder (distillation-llm) to "
                   "compare against.")
    p.add_argument("--reanalyze", type=Path, metavar="RUN_DIR",
                   help="Re-run the analysis on a saved stated run; no API calls.")
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.reanalyze:
        print(analyse(args.reanalyze, args.matrix, args.fuel, args.revealed))
        return 0
    if not args.model:
        print("error: --model is required (or use --reanalyze)", file=sys.stderr)
        return 2
    config = StatedConfig(
        model=args.model, n=args.n, temperature=args.temperature,
        matrix_path=args.matrix, output_root=args.output_root, spec_path=args.spec,
        show_zoo=args.show_zoo, fuel=args.fuel, revealed=args.revealed)
    print(f"Sampling {config.n} programs from {config.model} ...")
    run_dir = run_stated(config)
    print(f"\nRun saved to {run_dir}")
    print((run_dir / "report.txt").read_text())
    return 0


if __name__ == "__main__":
    sys.exit(main())
