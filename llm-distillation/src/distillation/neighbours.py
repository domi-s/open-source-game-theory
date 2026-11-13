"""Nearest library bot for each stated program, by tree edit distance.

Answers "what is this bot closest to?" even when it is not identical to anything: an
inverted-polarity PrudentBot is a library bot plus two edits, whatever its outcomes.
Distances are computed by the app's Zhang-Shasha implementation (``distance_worker.py``,
one process for the whole table) over the lossless trees of ``tree.py``.
"""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path

from .resolve import iter_library_programs
from .tree import program_tree

WORKER = Path(__file__).resolve().parent / "distance_worker.py"


def library_trees(bots_dir: Path) -> dict[str, tuple]:
    """Trees of the library bots that are plain ``Prog``; the others cannot be compared."""
    trees = ((name, program_tree(program)) for name, program in iter_library_programs(bots_dir))
    return {name: tree for name, tree in trees if tree is not None}


def edit_distances(app_dir: Path, programs: dict[str, tuple],
                   library: dict[str, tuple]) -> dict[str, dict[str, int]]:
    """``{program id: {library bot: distance}}``, computed in the app's environment."""
    proc = subprocess.run(
        ["uv", "run", "--directory", str(app_dir), "python", str(WORKER)],
        input=json.dumps({"programs": programs, "library": library}),
        capture_output=True, encoding="utf-8", env={**os.environ, "PYTHONUTF8": "1"})
    if proc.returncode != 0:
        raise RuntimeError(f"distance worker failed:\n{proc.stderr}")
    return json.loads(proc.stdout.strip().splitlines()[-1])


def nearest(distances: dict[str, int]) -> dict:
    """The closest library bots (all that tie) and their distance."""
    best = min(distances.values())
    return {"nearest": sorted(n for n, d in distances.items() if d == best), "distance": best}


def nearest_library_bots(app_dir: Path, bots_dir: Path, programs: dict[str, str],
                         distance_fn=edit_distances) -> dict[str, dict]:
    """For each ``{id: canonical program}``, its nearest library bots. Programs that are
    not plain ``Prog`` are left out (``None`` tree); so are library bots like that."""
    trees = {pid: program_tree(p) for pid, p in programs.items() if p}
    trees = {pid: t for pid, t in trees.items() if t is not None}
    library = library_trees(bots_dir)
    if not trees or not library:
        return {}
    return {pid: nearest(d) for pid, d in distance_fn(app_dir, trees, library).items()}
