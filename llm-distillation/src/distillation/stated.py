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

from .data import ReferenceLibrary, load_library
from .fitting import fit_all, fit_binomial
from .openrouter import make_client
from .pipeline import API_KEY_ENV, DEFAULT_MATRIX, DEFAULT_OUTPUT_ROOT
from .progress import Progress
from .reporting import format_report

REPO = Path(__file__).resolve().parents[3]
DEFAULT_SPEC = REPO / "engine/PrisonersDilemma/Research/Notes/PROG_LANGUAGE_SPEC_NO_EXAMPLES.md"
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
    matrix_path: Path = DEFAULT_MATRIX
    output_root: Path = DEFAULT_OUTPUT_ROOT
    spec_path: Path = DEFAULT_SPEC
    app_dir: Path = DEFAULT_APP
    sample_only: bool = False  # stop once the replies are saved
    from_run: Path | None = None  # profile this run's saved replies; no sampling
    reprofile: bool = False  # with from_run: ignore results already saved in bots.json


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
        input=source, capture_output=True, encoding="utf-8",
        env={**os.environ, "PYTHONUTF8": "1"})  # worker's stdin/stdout are UTF-8 too
    if proc.returncode != 0:
        raise RuntimeError(f"lean worker failed for {name}:\n{proc.stderr}")
    return json.loads(proc.stdout.strip().splitlines()[-1])


def _new_run_dir(config: StatedConfig, bot_order) -> Path:
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
    }, indent=2), encoding="utf-8")
    return run_dir


def _sample(config: StatedConfig, run_dir: Path) -> list[dict]:
    """Query the model ``n`` times, saving the replies after each one."""
    prompt = PROMPT_TEMPLATE.format(spec=config.spec_path.read_text(encoding="utf-8"))

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
        (run_dir / "raw_responses.json").write_text(json.dumps(responses, indent=2),
                                                    encoding="utf-8")
        progress.done += 1
    progress.clear()
    return responses


def run_stated(config: StatedConfig) -> Path:
    library = load_library(config.matrix_path)

    if config.from_run is not None:
        run_dir = config.from_run
        responses = json.loads((run_dir / "raw_responses.json").read_text(encoding="utf-8"))
    else:
        run_dir = _new_run_dir(config, library.bots)
        responses = _sample(config, run_dir)
        if config.sample_only:
            return run_dir

    # Results are saved after every bot, so an interrupted --from-run resumes here.
    finished = {} if config.reprofile else _load_finished(run_dir)
    bots = []
    for r in responses:
        name = f"StatedBot{r['index']}"
        source = extract_bot(r["raw"], name)
        entry = {"index": r["index"], "name": name, "source": source}
        if source is None:
            entry.update(valid=False, error="no ```lean block defining MyBot")
        elif finished.get(r["index"], {}).get("source") == source:
            print(f"  Lean: {name} already saved, skipping", file=sys.stderr)
            entry = finished[r["index"]]
        else:
            print(f"  Lean: {name} ...", file=sys.stderr)
            entry.update(run_in_lean(config.app_dir, name, source, library.bots))
        bots.append(entry)
        _save_results(run_dir, library, bots, len(responses))
    return run_dir


def _load_finished(run_dir: Path) -> dict[int, dict]:
    """Bots already profiled in this run, by index; empty if none were saved."""
    path = run_dir / "bots.json"
    if not path.exists():
        return {}
    return {b["index"]: b for b in json.loads(path.read_text(encoding="utf-8"))}


def _write_text(path: Path, text: str) -> None:
    """Replace ``path`` in one step, so a kill mid-write cannot corrupt saved results."""
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, path)


def _save_results(run_dir: Path, library: ReferenceLibrary, bots: list[dict],
                  total: int) -> None:
    """Write bots.json, cooperation_vector.json and report.txt for the bots done so far."""
    valid = [b for b in bots if b["valid"]]
    c, n = np.zeros(library.n), np.zeros(library.n)
    for b in valid:
        cells = {cell["opponent"]: cell for cell in b["cells"]}
        for j, opp in enumerate(library.bots):
            if cells[opp]["verdict"] == "stable":
                n[j] += 1
                c[j] += cells[opp]["my_action"] == "C"
    x = np.divide(c, n, out=np.full(library.n, np.nan), where=n > 0)

    lines = [f"PARTIAL: {len(bots)}/{total} replies processed so far"] if len(bots) < total else []
    lines += [f"Valid bots: {len(valid)}/{len(bots)}",
              "Per opponent: cooperations / bots with a stable Lean verdict"]
    lines += [f"  {b}: {int(ci)}/{int(ni)}" for b, ci, ni in zip(library.bots, c, n)]
    if n.all():
        fits = fit_all(library.R, x) + [fit_binomial(library.R, c, n)]
        report = "\n".join(lines) + "\n\n" + format_report(library, fits, x)
    else:
        report = "\n".join(lines + ["", "Not fit: some opponent has no stable verdict."]) + "\n"

    _write_text(run_dir / "bots.json", json.dumps(bots, indent=2))
    xs = [None if np.isnan(v) else float(v) for v in x]
    _write_text(run_dir / "cooperation_vector.json", json.dumps({
        "bots": list(library.bots),
        "x": xs,
        "by_bot": dict(zip(library.bots, xs)),
        "cooperations": c.astype(int).tolist(),
        "stable_verdicts": n.astype(int).tolist(),
    }, indent=2))
    _write_text(run_dir / "report.txt", report)
