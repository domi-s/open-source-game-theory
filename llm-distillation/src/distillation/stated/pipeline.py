"""Approach 3 ("stated strategy"): sample Prog programs from an LLM, profile, fit.

    n calls ──► raw replies ──► judge (extract + parse + lint) ──► valid programs
            ──► profile each against the library (sound, partial evaluator)
            ──► x̄ (average) ──► fits;  per-sample fits ──► type distribution

Each run writes ``runs/<timestamp>_stated_<model-slug>/``:

* ``metadata.json``        -- mode, model, n, temperature, flags, spec sha256.
* ``prompt.txt``           -- the exact prompt sent (spec embedded).
* ``raw_responses.json``   -- every reply, written INCREMENTALLY (a crash keeps
                              what was paid for; ``--reanalyze`` resumes analysis).
* ``programs.json``        -- per sample: source, validity, errors/warnings, the
                              expanded program, and every profile cell with its
                              provenance.
* ``stated_vector.json``   -- x̄, counts, coverage (same ``by_bot`` shape as the
                              revealed pipeline's ``cooperation_vector.json``).
* ``report.txt``           -- clusters, coverage, both aggregation orders, and the
                              stated-vs-revealed table when ``--revealed`` is given.
"""

from __future__ import annotations

import hashlib
import json
import os
import sys
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

from ..data import load_library
from ..openrouter import make_client
from .aggregate import build_report
from .evaluate import MatrixOracle, profile
from .parse import judge
from .prog import show
from .prompt import DEFAULT_SPEC_PATH, MAIN_NAME, build_stated_prompt
from .zoo import zoo_names, zoo_scope

API_KEY_ENV = "OPENROUTER_API_KEY"


@dataclass
class StatedConfig:
    model: str
    n: int = 30
    temperature: float = 1.0
    matrix_path: Path = Path("data/payoff_matrix.csv")
    output_root: Path = Path("runs")
    spec_path: Path = DEFAULT_SPEC_PATH
    show_zoo: bool = False
    fuel: int = 300
    revealed: Path | None = None


def _slug(model: str) -> str:
    return model.replace("/", "-").replace(":", "-")


def query_text(client, model: str, prompt: str, temperature: float) -> str:
    response = client.chat.completions.create(
        model=model, messages=[{"role": "user", "content": prompt}],
        temperature=temperature)
    return response.choices[0].message.content or ""


def run_stated(config: StatedConfig, client=None) -> Path:
    """Sample ``n`` programs, then analyse. ``client`` is injectable for tests."""
    spec = Path(config.spec_path).read_text()
    prompt = build_stated_prompt(spec, config.show_zoo)
    load_library(config.matrix_path)  # fail fast on a bad matrix, before paying

    if client is None:
        api_key = os.environ.get(API_KEY_ENV)
        if not api_key:
            raise RuntimeError(f"Environment variable {API_KEY_ENV} is not set.")
        client = make_client(api_key)

    timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    run_dir = config.output_root / f"{timestamp}_stated_{_slug(config.model)}"
    run_dir.mkdir(parents=True, exist_ok=True)
    (run_dir / "prompt.txt").write_text(prompt)
    (run_dir / "metadata.json").write_text(json.dumps({
        "mode": "stated",
        "model": config.model,
        "n": config.n,
        "temperature": config.temperature,
        "timestamp": timestamp,
        "matrix_path": str(config.matrix_path),
        "spec_path": str(config.spec_path),
        "spec_sha256": hashlib.sha256(spec.encode()).hexdigest(),
        "show_zoo": config.show_zoo,
        "fuel": config.fuel,
        "budget_convention": "same-k: every budget parameter of a sample is set to "
                             "the opponents' k; cells are read at large k",
    }, indent=2))

    raw: list[dict] = []
    start = time.monotonic()
    for i in range(config.n):
        sys.stderr.write(f"\r\033[2K\033[90mcall {i + 1}/{config.n} | "
                         f"{time.monotonic() - start:.0f}s\033[0m")
        sys.stderr.flush()
        try:
            text, err = query_text(client, config.model, prompt, config.temperature), None
        except Exception as exc:  # keep the run going; record the failure
            text, err = "", f"{type(exc).__name__}: {exc}"
        raw.append({"index": i, "raw": text, "api_error": err})
        (run_dir / "raw_responses.json").write_text(json.dumps(raw, indent=2))
    sys.stderr.write("\r\033[2K")

    analyse(run_dir, config.matrix_path, config.fuel, config.revealed)
    return run_dir


def analyse(run_dir: Path, matrix_path: Path, fuel: int = 300,
            revealed: Path | None = None) -> str:
    """(Re)run judging, profiling and fitting on a run folder's saved replies."""
    library = load_library(matrix_path)
    oracle = MatrixOracle.from_library(library.bots, library.R)
    raw = json.loads((run_dir / "raw_responses.json").read_text())

    samples = [judge(r["index"], r["raw"], zoo_scope(), MAIN_NAME) for r in raw]
    for s, r in zip(samples, raw):
        if r.get("api_error"):
            s.errors.insert(0, f"api error: {r['api_error']}")
    profiles = {s.index: profile(s.program, s.params, oracle, fuel)
                for s in samples if s.valid}

    revealed_x = None
    if revealed is not None:
        revealed_x = json.loads((Path(revealed) / "cooperation_vector.json")
                                .read_text())["by_bot"]
    report, agg = build_report(library, samples, profiles, revealed_x)

    (run_dir / "programs.json").write_text(json.dumps([{
        "index": s.index,
        "valid": s.valid,
        "errors": s.errors,
        "warnings": s.warnings,
        "name": s.name,
        "params": list(s.params),
        "source": s.source,
        "expanded": show(s.program, zoo_names()) if s.program is not None else None,
        "profile": {o: {"value": c.value, "provenance": list(c.provenance),
                        "reason": c.reason}
                    for o, c in profiles.get(s.index, {}).items()},
    } for s in samples], indent=2))

    x = [None if v != v else float(v) for v in agg.x]  # NaN -> null
    (run_dir / "stated_vector.json").write_text(json.dumps({
        "bots": list(library.bots),
        "x": x,
        "by_bot": dict(zip(library.bots, x)),
        "cooperations": agg.c.astype(int).tolist(),
        "determined": agg.n.astype(int).tolist(),
        "undetermined": agg.undetermined.astype(int).tolist(),
        "nonterminating": agg.nonterminating.astype(int).tolist(),
        "valid_programs": agg.n_valid,
        "samples": agg.n_total,
    }, indent=2))
    (run_dir / "report.txt").write_text(report)
    return report
