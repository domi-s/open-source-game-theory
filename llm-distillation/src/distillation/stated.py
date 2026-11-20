"""Stated-strategy pipeline: the LLM writes its strategy as a Prog bot; Lean profiles it.

Steps, each in its own module and writing its own file in the run folder:
sample (``sample.py``), canonicalise (``classes.py``), distances (``distances.py``),
outcomes (this file: cells from theorems, then Lean, then open; then the fit).
See ``STATED.md``.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

import numpy as np

from .canonical import canonicalise, program_key
from .classes import canonicalise_programs
from .data import ReferenceLibrary, load_library
from .distances import compute_distances
from .fitting import fit_all, fit_binomial
from .neighbours import nearest
from .pipeline import DEFAULT_MATRIX, DEFAULT_OUTPUT_ROOT
from .reporting import format_report
from .resolve import (DEFAULT_BOTS_DIR, DEFAULT_THEOREMS, THEOREM, load_library_programs,
                      load_theorems, tag_eval_cell, theorem_cells)
from .sample import extract_programs, sample

REPO = Path(__file__).resolve().parents[3]
DEFAULT_SPEC = REPO / "engine/PrisonersDilemma/Research/Notes/PROG_LANGUAGE_SPEC_NO_EXAMPLES.md"
DEFAULT_APP = REPO / "app"
WORKER = Path(__file__).resolve().parent / "lean_worker.py"
RESULT_KEYS = ("valid", "error", "budgets", "cells")  # what lean_worker.py returns

STEPS = ("sample", "canonicalise", "distances", "outcomes")

@dataclass
class StatedConfig:
    """Configuration for a stated-strategy run."""

    model: str
    n: int = 30
    temperature: float = 1.0
    matrix_path: Path = DEFAULT_MATRIX
    output_root: Path = DEFAULT_OUTPUT_ROOT
    spec_path: Path = DEFAULT_SPEC
    app_dir: Path = DEFAULT_APP
    steps: tuple[str, ...] = STEPS  # which steps to run, in order
    from_run: Path | None = None  # continue this run folder instead of sampling a new one
    reprofile: bool = False  # with from_run: ignore results already saved in bots.json
    use_library: bool = True  # resolve cells from library theorems before Lean
    bots_dir: Path = DEFAULT_BOTS_DIR  # the library bots a stated bot may be identical to
    theorems_path: Path = DEFAULT_THEOREMS  # their proved outcomes

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
    """Make a new run folder and write its metadata.json."""
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

def run_stated(config: StatedConfig) -> Path:
    """Run the stated-strategy pipeline, returning the run folder."""
    library = load_library(config.matrix_path)
    run_dir = config.from_run or _new_run_dir(config, library.bots)
    explicit = config.steps != STEPS  # a chosen step is redone even if its file exists

    if "sample" in config.steps:
        if config.from_run is None:
            sample(run_dir, config.model, config.n, config.temperature, config.spec_path)
        extract_programs(run_dir)
    if "canonicalise" in config.steps:
        canonicalise_programs(run_dir)
    classes = (json.loads((run_dir / "classes.json").read_text(encoding="utf-8"))
               if {"distances", "outcomes"} & set(config.steps) else [])
    if "distances" in config.steps and (explicit or not (run_dir / "distances.json").exists()):
        compute_distances(run_dir, classes, config.bots_dir, config.app_dir)
    if "outcomes" in config.steps:
        _outcomes(config, run_dir, library, classes)
    return run_dir

def _outcomes(config: StatedConfig, run_dir: Path, library: ReferenceLibrary,
              classes: list[dict]) -> None:
    """One resolution per class, saved after each, so an interrupted run resumes here."""
    finished = {} if config.reprofile else _load_finished(run_dir)
    twins = load_library_programs(config.bots_dir) if config.use_library else {}
    theorems = load_theorems(config.theorems_path) if config.use_library else {}
    near = _nearest_bots(run_dir) if config.use_library else {}
    print(f"  {sum(c['count'] for c in classes)} samples -> {len(classes)} distinct programs",
          file=sys.stderr)
    bots = []
    for entry in classes:
        key = canonicalise(entry["source"]) if entry["source"] else None
        resolve_entry(entry, library.bots, twins, theorems, finished.get(key), config.app_dir)
        entry["neighbours"] = near.get(entry["name"])
        bots.append(entry)
        _save_results(run_dir, library, bots, len(classes))

def _nearest_bots(run_dir: Path) -> dict[str, dict]:
    """Nearest library bots per class, from ``distances.json`` (empty if step 3a was not run)."""
    path = run_dir / "distances.json"
    if not path.exists():
        return {}
    rows = json.loads(path.read_text(encoding="utf-8"))["library"]
    return {name: nearest(row) for name, row in rows.items() if row}

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
