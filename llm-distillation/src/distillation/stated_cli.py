"""Command-line entry point for the stated-strategy pipeline.

Usage::

    distillation-stated --model anthropic/claude-3.5-sonnet [--n 30]

Requires ``OPENROUTER_API_KEY``, ``uv``, and a built engine (``lake build``).
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from .stated import DEFAULT_APP, DEFAULT_SPEC, StatedConfig, run_stated


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="distillation-stated",
        description="Ask an LLM to write its strategy as a Prog bot, profile the "
        "valid bots in Lean against every library bot, then fit.",
    )
    parser.add_argument("--model", required=True, help="OpenRouter model id.")
    parser.add_argument("--n", type=int, default=30,
                        help="Bots to sample. Default: 30.")
    parser.add_argument("--temperature", type=float, default=1.0,
                        help="Sampling temperature. Default: 1.0.")
    parser.add_argument("--matrix", type=Path, default=Path("data/payoff_matrix.csv"),
                        help="Path to the payoff matrix CSV.")
    parser.add_argument("--output-root", type=Path, default=Path("runs"),
                        help="Root folder for run outputs. Default: runs.")
    parser.add_argument("--spec", type=Path, default=DEFAULT_SPEC,
                        help="Prog language specification put in the prompt.")
    parser.add_argument("--app-dir", type=Path, default=DEFAULT_APP,
                        help="The app project, whose environment runs Lean.")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    config = StatedConfig(
        model=args.model,
        n=args.n,
        temperature=args.temperature,
        matrix_path=args.matrix,
        output_root=args.output_root,
        spec_path=args.spec,
        app_dir=args.app_dir,
    )
    print(f"Sampling {config.n} bots from model {config.model} ...")
    run_dir = run_stated(config)
    print(f"\nRun saved to {run_dir}")
    print((run_dir / "report.txt").read_text())
    return 0


if __name__ == "__main__":
    sys.exit(main())
