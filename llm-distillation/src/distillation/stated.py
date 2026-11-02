"""Stated-strategy pipeline: the LLM writes its strategy as a Prog bot; Lean profiles it.

For each of ``n`` samples the model gets the Prog language specification and is
asked to write ``MyBot``, the program that plays as it would. The reply's last
```lean block is extracted (like ``parse_action``: last occurrence wins) and
renamed ``StatedBot<i>``. Lean then decides validity (does it compile?) and the
bot's action against every library bot (the engine's certified evaluator, via
``lean_worker.py`` in the app environment). The cooperation rate against each
opponent over the valid bots is ``x``, fit exactly like the revealed pipeline.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

import numpy as np

from .data import load_library
from .fitting import fit_all, fit_binomial
from .openrouter import make_client
from .progress import Progress
from .reporting import format_report

API_KEY_ENV = "OPENROUTER_API_KEY"
REPO = Path(__file__).resolve().parents[3]
DEFAULT_SPEC = REPO / "engine/PrisonersDilemma/Research/Notes/PROG_LANGUAGE_SPEC.md"
DEFAULT_APP = REPO / "app"
WORKER = Path(__file__).resolve().parent / "lean_worker.py"

PROMPT_TEMPLATE = """\
You are playing a one-shot Prisoner's Dilemma under *maximum transparency*: your
opponent can read your full source code and you can read theirs.

Write your own strategy for this game as a bot in the `Prog` language specified
below: the program that plays exactly as you would against any opponent. Name it
`MyBot`. Follow the output contract in section 12 of the specification (a complete
Lean file: imports, `namespace PD.Bots`, the definition, `end PD.Bots`).

Reason as much as you like, then give your final answer as one ```lean code block.

{spec}
"""

_LEAN_BLOCK_RE = re.compile(r"```lean4?\s*\n(.*?)```", re.DOTALL)


@dataclass
class StatedConfig:
    model: str
    n: int = 30
    temperature: float = 1.0
    matrix_path: Path = Path("data/payoff_matrix.csv")
    output_root: Path = Path("runs")
    spec_path: Path = DEFAULT_SPEC
    app_dir: Path = DEFAULT_APP


def extract_bot(text: str, name: str) -> str | None:
    """The last ```lean block, with ``MyBot`` renamed to ``name``; None if absent."""
    blocks = _LEAN_BLOCK_RE.findall(text)
    if not blocks or not re.search(r"\bdef\s+MyBot\b", blocks[-1]):
        return None
    return re.sub(r"\bMyBot\b", name, blocks[-1])


def run_in_lean(app_dir: Path, name: str, source: str, opponents) -> dict:
    """Compile + profile one bot in Lean (see ``lean_worker.py``)."""
    proc = subprocess.run(
        ["uv", "run", "--directory", str(app_dir), "python", str(WORKER),
         "--name", name, "--opponents", ",".join(opponents)],
        input=source, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"lean worker failed for {name}:\n{proc.stderr}")
    return json.loads(proc.stdout.strip().splitlines()[-1])


def run_stated(config: StatedConfig) -> Path:
    library = load_library(config.matrix_path)
    prompt = PROMPT_TEMPLATE.format(spec=config.spec_path.read_text())

    api_key = os.environ.get(API_KEY_ENV)
    if not api_key:
        raise RuntimeError(f"Environment variable {API_KEY_ENV} is not set.")
    client = make_client(api_key)

    responses = []
    progress = Progress(1, config.n)
    for i in range(config.n):
        progress.show(0, "sampling", i)
        reply = client.chat.completions.create(
            model=config.model, messages=[{"role": "user", "content": prompt}],
            temperature=config.temperature)
        responses.append({"index": i, "raw": reply.choices[0].message.content or ""})
        progress.done += 1
    progress.clear()

    bots = []
    for r in responses:
        name = f"StatedBot{r['index']}"
        source = extract_bot(r["raw"], name)
        entry = {"index": r["index"], "name": name, "source": source}
        if source is None:
            entry.update(valid=False, error="no ```lean block defining MyBot")
        else:
            print(f"  Lean: {name} ...", file=sys.stderr)
            entry.update(run_in_lean(config.app_dir, name, source, library.bots))
        bots.append(entry)

    valid = [b for b in bots if b["valid"]]
    c, n = np.zeros(library.n), np.zeros(library.n)
    for b in valid:
        cells = {cell["opponent"]: cell for cell in b["cells"]}
        for j, opp in enumerate(library.bots):
            if cells[opp]["verdict"] == "stable":
                n[j] += 1
                c[j] += cells[opp]["my_action"] == "C"
    x = np.divide(c, n, out=np.full(library.n, np.nan), where=n > 0)

    lines = [f"Valid bots: {len(valid)}/{config.n}",
             "Per opponent: cooperations / bots with a stable Lean verdict"]
    lines += [f"  {b}: {int(ci)}/{int(ni)}" for b, ci, ni in zip(library.bots, c, n)]
    if n.all():
        fits = fit_all(library.R, x) + [fit_binomial(library.R, c, n)]
        report = "\n".join(lines) + "\n\n" + format_report(library, fits, x)
    else:
        report = "\n".join(lines + ["", "Not fit: some opponent has no stable verdict."]) + "\n"

    return _write_outputs(config, library.bots, x, c, n, responses, bots, report)


def _write_outputs(config, bot_order, x, c, n, responses, bots, report) -> Path:
    timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    slug = config.model.replace("/", "-").replace(":", "-")
    run_dir = config.output_root / f"{timestamp}_stated_{slug}"
    run_dir.mkdir(parents=True, exist_ok=True)

    (run_dir / "metadata.json").write_text(json.dumps({
        "mode": "stated",
        "model": config.model,
        "n": config.n,
        "temperature": config.temperature,
        "timestamp": timestamp,
        "matrix_path": str(config.matrix_path),
        "spec_path": str(config.spec_path),
        "bots": list(bot_order),
    }, indent=2))
    (run_dir / "raw_responses.json").write_text(json.dumps(responses, indent=2))
    (run_dir / "bots.json").write_text(json.dumps(bots, indent=2))
    xs = [None if np.isnan(v) else float(v) for v in x]
    (run_dir / "cooperation_vector.json").write_text(json.dumps({
        "bots": list(bot_order),
        "x": xs,
        "by_bot": dict(zip(bot_order, xs)),
        "cooperations": c.astype(int).tolist(),
        "stable_verdicts": n.astype(int).tolist(),
    }, indent=2))
    (run_dir / "report.txt").write_text(report)
    return run_dir
