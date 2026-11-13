"""Command-line entry point for the stated-strategy pipeline.

Usage::

    distillation-stated --model anthropic/claude-3.5-sonnet [--n 30]
    distillation-stated --model anthropic/claude-3.5-sonnet --sample-only
    distillation-stated --from-run runs/<run folder>

Requires ``OPENROUTER_API_KEY``, ``uv``, and a built engine (``lake build``).
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from .pipeline import DEFAULT_MATRIX, DEFAULT_OUTPUT_ROOT
from .stated import DEFAULT_APP, DEFAULT_SPEC, StatedConfig, run_stated


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="distillation-stated",
        description="Ask an LLM to write its strategy as a Prog bot, profile the "
        "valid bots in Lean against every library bot, then fit.",
    )
    parser.add_argument("--model", help="OpenRouter model id. Required unless --from-run.")
    parser.add_argument("--n", type=int, default=30,
                        help="Bots to sample. Default: 30.")
    parser.add_argument("--temperature", type=float, default=1.0,
                        help="Sampling temperature. Default: 1.0.")
    parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX,
                        help="Path to the payoff matrix CSV.")
    parser.add_argument("--output-root", type=Path, default=DEFAULT_OUTPUT_ROOT,
                        help="Root folder for run outputs. Default: runs.")
    parser.add_argument("--spec", type=Path, default=DEFAULT_SPEC,
                        help="Prog language specification put in the prompt.")
    parser.add_argument("--app-dir", type=Path, default=DEFAULT_APP,
                        help="The app project, whose environment runs Lean.")
    parser.add_argument("--sample-only", action="store_true",
                        help="Save the model's replies and stop, skipping Lean.")
    parser.add_argument("--from-run", type=Path,
                        help="Run Lean and the fit on this run folder's saved replies, "
                        "resuming after any bots already saved.")
    parser.add_argument("--reprofile", action="store_true",
                        help="With --from-run: redo every bot, ignoring saved results.")
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if not args.model and not args.from_run:
        parser.error("--model is required unless --from-run is given")
    if args.sample_only and args.from_run:
        parser.error("--sample-only and --from-run do not combine")
    if args.reprofile and not args.from_run:
        parser.error("--reprofile requires --from-run")
    config = StatedConfig(
        model=args.model or "",
        n=args.n,
        temperature=args.temperature,
        matrix_path=args.matrix,
        output_root=args.output_root,
        spec_path=args.spec,
        app_dir=args.app_dir,
        sample_only=args.sample_only,
        from_run=args.from_run,
        reprofile=args.reprofile,
    )
    if not args.from_run:
        print(f"Sampling {config.n} bots from model {config.model} ...")
    run_dir = run_stated(config)
    print(f"\nRun saved to {run_dir}")
    if args.sample_only:
        print(f'Profile it later with: --from-run "{run_dir}"')
        return 0
    print((run_dir / "report.txt").read_text(encoding="utf-8"))
    return 0


if __name__ == "__main__":
    sys.exit(main())