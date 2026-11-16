"""Stated-strategy pipeline: the LLM writes its strategy as a Prog bot; Lean profiles it.

For each of ``n`` samples the model gets the Prog language specification and is
asked to write ``MyBot``, the program that plays as it would. The reply's last
```lean block is extracted (like ``parse_action``: last occurrence wins) and
renamed ``StatedBot<i>``. Samples that wrote the same program (up to comments, bot
name, budget parameters and layout: ``canonical.py``) are grouped and resolved once per
distinct program; the group size is that program's sample weight. Each cell (the
program's action against one library bot) comes from a library theorem if the program IS
a library bot, else from Lean (the engine's certified evaluator, via ``lean_worker.py``
in the app environment), else it is open (``resolve.py``). The weighted cooperation rate
against each opponent over the proved cells is ``x``, fit exactly like the revealed
pipeline.
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

from .canonical import DEFAULT_NAME, budget_params, canonicalise, program_key
from .data import ReferenceLibrary, load_library
from .fitting import fit_all, fit_binomial
from .neighbours import nearest_library_bots
from .openrouter import make_client
from .pipeline import API_KEY_ENV, DEFAULT_MATRIX, DEFAULT_OUTPUT_ROOT
from .progress import Progress
from .reporting import format_report
from .resolve import (DEFAULT_BOTS_DIR, DEFAULT_THEOREMS, THEOREM, load_library_programs,
                      load_theorems, tag_eval_cell, theorem_cells)

REPO = Path(__file__).resolve().parents[3]
DEFAULT_SPEC = REPO / "engine/PrisonersDilemma/Research/Notes/PROG_LANGUAGE_SPEC_NO_EXAMPLES.md"
DEFAULT_APP = REPO / "app"
WORKER = Path(__file__).resolve().parent / "lean_worker.py"
RESULT_KEYS = ("valid", "error", "budgets", "cells")  # what lean_worker.py returns

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
    use_library: bool = True  # resolve cells from library theorems before Lean
    bots_dir: Path = DEFAULT_BOTS_DIR  # the library bots a stated bot may be identical to
    theorems_path: Path = DEFAULT_THEOREMS  # their proved outcomes


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

    # One resolution per DISTINCT program; its sample count becomes its weight.
    # Results are saved after every program, so an interrupted --from-run resumes here.
    finished = {} if config.reprofile else _load_finished(run_dir)
    groups = group_samples(responses)
    twins = load_library_programs(config.bots_dir) if config.use_library else {}
    theorems = load_theorems(config.theorems_path) if config.use_library else {}
    near = _neighbours(config, groups) if config.use_library else {}
    print(f"  {len(responses)} samples -> {len(groups)} distinct programs", file=sys.stderr)
    bots = []
    for key, entry in groups.items():
        resolve_entry(entry, library.bots, twins, theorems, finished.get(key),
                      config.app_dir)
        entry["neighbours"] = near.get(entry["name"])
        bots.append(entry)
        _save_results(run_dir, library, bots, len(groups))
    return run_dir


def _neighbours(config: StatedConfig, groups: dict) -> dict[str, dict]:
    """Nearest library bot per program. A diagnostic: if it cannot run, skip the table."""
    programs = {e["name"]: program_key(e["source"]) for e in groups.values() if e["source"]}
    try:
        return nearest_library_bots(config.app_dir, config.bots_dir, programs)
    except (RuntimeError, OSError, ValueError) as err:
        print(f"  nearest-bot table skipped: {err}", file=sys.stderr)
        return {}


def resolve_entry(entry: dict, opponents, twins: dict, theorems: dict,
                  saved: dict | None, app_dir: Path) -> None:
    """Give ``entry`` its validity and one cell per opponent, each tagged with its source.

    Order per cell: library theorem (the program IS a library bot with a proved row),
    else Lean eval, else open. Lean only runs for the cells no theorem covers, and not
    at all when a theorem covers every opponent: an identical program needs no compile.
    ``saved`` is this program's result from an earlier run, reused when it covers what
    is still needed.
    """
    name, source = entry["name"], entry["source"]
    if source is None:
        entry.update(valid=False, error="no ```lean block defining MyBot")
        return
    library_bots = twins.get(program_key(source), [])
    cells = theorem_cells(library_bots, opponents, theorems)
    if library_bots:
        entry["library_bots"] = library_bots
    need = [o for o in opponents if o not in cells]

    if not need:
        print(f"  {name} (x{entry['count']}): all cells from the theorems of "
              f"{'/'.join(library_bots)}, no Lean", file=sys.stderr)
        entry.update(valid=True, compiled=False, budgets=[],
                     cells=[cells[o] for o in opponents])
        return

    saved_cells = ({c["opponent"]: c for c in saved.get("cells", [])}
                   if saved and saved.get("valid") else {})
    if saved and saved.get("valid") is False:
        result = {k: v for k, v in saved.items() if k in RESULT_KEYS}
    elif saved and all(o in saved_cells for o in need):
        result = {"valid": True, "budgets": saved.get("budgets", []),
                  "cells": [saved_cells[o] for o in need]}
    else:
        print(f"  Lean: {name} (x{entry['count']}), {len(need)} of {len(opponents)} cells "
              "...", file=sys.stderr)
        result = run_in_lean(app_dir, name, source, need)
    if not result["valid"]:
        entry.update(valid=False, error=result.get("error", ""))
        return
    lean = {c["opponent"]: tag_eval_cell(c) for c in result["cells"]}
    entry.update(valid=True, compiled=True, budgets=result["budgets"],
                 cells=[cells.get(o) or lean[o] for o in opponents])


def group_samples(responses: list[dict]) -> dict[str | None, dict]:
    """Group replies by canonical program (see ``canonical.py``), in first-seen order.

    Key: the canonical source, or None for replies with no usable bot. Each entry is
    named after its first sample and carries ``indices``/``count`` (its weight). The
    entry's ``source`` is the canonical program under that name — what Lean runs.
    """
    groups: dict[str | None, dict] = {}
    for r in responses:
        raw = extract_bot(r["raw"], DEFAULT_NAME)
        key = canonicalise(raw) if raw is not None else None
        if key not in groups:
            name = f"StatedBot{r['index']}"
            groups[key] = {"index": r["index"], "name": name, "indices": [], "count": 0,
                           "budget_params": 0 if raw is None else budget_params(raw),
                           "source": None if raw is None else canonicalise(raw, name)}
        groups[key]["indices"].append(r["index"])
        groups[key]["count"] += 1
    return groups


def _load_finished(run_dir: Path) -> dict[str, dict]:
    """Programs already profiled in this run, by canonical source; empty if none saved.

    Keyed by ``canonicalise`` of the saved source, so results from runs saved before
    deduplication (one entry per sample) are reused too.
    """
    path = run_dir / "bots.json"
    if not path.exists():
        return {}
    return {canonicalise(b["source"]): b
            for b in json.loads(path.read_text(encoding="utf-8")) if b.get("source")}


def _write_text(path: Path, text: str) -> None:
    """Replace ``path`` in one step, so a kill mid-write cannot corrupt saved results."""
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, path)


def _save_results(run_dir: Path, library: ReferenceLibrary, bots: list[dict],
                  total: int) -> None:
    """Write bots.json, cooperation_vector.json and report.txt for the programs done so far.

    ``bots`` holds one entry per distinct program; its ``count`` (default 1) is the
    number of samples that wrote it, and weights it in every tally, so the result is
    exactly what profiling each sample separately would give. ``total`` is the number
    of distinct programs expected.
    """
    weight = lambda b: b.get("count", 1)
    valid = [b for b in bots if b["valid"]]
    samples = sum(weight(b) for b in bots)
    valid_samples = sum(weight(b) for b in valid)
    c, n = np.zeros(library.n), np.zeros(library.n)
    by_source = {opp: dict.fromkeys(CATEGORIES, 0) for opp in library.bots}
    for b in valid:
        cells = {cell["opponent"]: cell for cell in b["cells"]}
        for j, opp in enumerate(library.bots):
            by_source[opp][_category(cells[opp])] += weight(b)
            if cells[opp]["verdict"] == "stable":
                n[j] += weight(b)
                c[j] += weight(b) * (cells[opp]["my_action"] == "C")
    x = np.divide(c, n, out=np.full(library.n, np.nan), where=n > 0)

    totals = {cat: sum(s[cat] for s in by_source.values()) for cat in CATEGORIES}
    proved = totals["theorem"] + totals["eval"]
    lines = ([f"PARTIAL: {len(bots)}/{total} distinct programs profiled so far"]
             if len(bots) < total else [])
    lines += [f"Distinct programs: {len(bots)} for {samples} samples",
              f"Valid bots: {valid_samples}/{samples}",
              f"Cells (valid bot x opponent, weighted by samples): "
              f"{valid_samples * library.n}",
              f"  proved by a library theorem: {totals['theorem']}",
              f"  proved by certified Lean eval: {totals['eval']}",
              f"  certified but budget-dependent (no single answer): {totals['k_dependent']}",
              f"  OPEN (no theorem, no certified eval): {totals['open']}",
              f"  -> {proved} of {valid_samples * library.n} cells carry a proved answer",
              f"Budget rule: every free budget parameter is the same k; "
              f"{sum(weight(b) for b in valid if b.get('budget_params', 0) > 1)} of "
              f"{valid_samples} valid samples had 2+ (any staggering through them is collapsed)",
              "Per opponent: cooperations / bots with a proved verdict, then where "
              "each valid bot's cell came from"]
    lines += [f"  {b}: {int(ci)}/{int(ni)}   [theorem {s['theorem']}, eval {s['eval']}, "
              f"k-dependent {s['k_dependent']}, open {s['open']}]"
              for b, ci, ni, s in zip(library.bots, c, n, by_source.values())]
    lines += _neighbour_lines(bots)

    # Fit on the opponents that HAVE a proved answer and list the rest: a missing
    # cell makes the fit weaker (fewer constraints), not impossible.
    fit_on = np.flatnonzero(n > 0)
    left_out = [library.bots[j] for j in np.flatnonzero(n == 0)]
    if len(fit_on):
        R, opponents = library.R[:, fit_on], tuple(library.bots[j] for j in fit_on)
        fits = fit_all(R, x[fit_on]) + [fit_binomial(R, c[fit_on], n[fit_on])]
        note = (f"Fit on {len(fit_on)} of {library.n} opponents. LEFT OUT (no proved answer "
                f"from any valid bot): {', '.join(left_out)}. Fewer constraints, so a "
                "weaker fit, not none.\n\n" if left_out else "")
        report = ("\n".join(lines) + "\n\n" + note
                  + format_report(library, fits, x[fit_on], opponents))
    else:
        report = "\n".join(lines + ["", "Not fit: no opponent has a proved answer."]) + "\n"

    _write_text(run_dir / "bots.json", json.dumps(bots, indent=2))
    xs = [None if np.isnan(v) else float(v) for v in x]
    _write_text(run_dir / "cooperation_vector.json", json.dumps({
        "bots": list(library.bots),
        "x": xs,
        "by_bot": dict(zip(library.bots, xs)),
        "cooperations": c.astype(int).tolist(),
        "stable_verdicts": n.astype(int).tolist(),
        "by_source": by_source,
        "left_out": left_out,
    }, indent=2))
    _write_text(run_dir / "open_cells.json", json.dumps(_open_cells(valid), indent=2))
    _write_text(run_dir / "report.txt", report)


CATEGORIES = ("theorem", "eval", "k_dependent", "open")


def _category(cell: dict) -> str:
    """Where a cell's answer stands: a library theorem, a certified Lean eval (one
    answer, or budget-dependent), or open. Cells saved before the source was recorded
    are classed by their verdict."""
    if cell.get("source") == THEOREM:
        return "theorem"
    return {"stable": "eval", "phase_dependent": "k_dependent"}.get(cell["verdict"], "open")


def _neighbour_lines(bots: list[dict]) -> list[str]:
    """The nearest-library-bot table: one line per distinct program."""
    lines = ["Nearest library bot per distinct program (tree edit distance, 0 = identical):"]
    for b in bots:
        near = b.get("neighbours")
        what = (f"{'/'.join(near['nearest'])}, distance {near['distance']}" if near
                else "not compared (no bot, or not plain Prog)")
        lines.append(f"  {b['name']} (x{b.get('count', 1)}): {what}")
    return lines


def _open_cells(valid_bots: list[dict]) -> list[dict]:
    """The blind spots: every (program, opponent) cell with no proved answer, in the
    shape the app's proof pipeline needs to pick it up (the bot's source + the opponent)."""
    return [{"opponent": cell["opponent"], "bot": b["name"], "indices": b.get("indices", []),
             "count": b.get("count", 1), "reason": cell.get("note") or cell["verdict"],
             "by_budget": cell.get("by_budget", {}), "source": b["source"]}
            for b in valid_bots for cell in b["cells"] if _category(cell) == "open"]
