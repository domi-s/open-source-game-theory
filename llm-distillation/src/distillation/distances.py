"""Step 3a. Distances. Tree edit distance from each class to every library bot and every other class."""

from __future__ import annotations

import json
from pathlib import Path

from .canonical import program_key
from .neighbours import edit_distances, library_trees
from .tree import program_tree

def compute_distances(run_dir: Path, classes: list[dict], bots_dir: Path, app_dir: Path,
                      distance_fn=edit_distances) -> dict:
    """Write ``distances.json``: ``{"library": {class: {bot: d}}, "classes": {class: {class: d}}}``.

    Library-vs-library distances are not computed. Programs that are not plain ``Prog``
    are left out.
    """
    trees = {c["name"]: program_tree(program_key(c["source"])) for c in classes if c["source"]}
    trees = {name: tree for name, tree in trees.items() if tree is not None}
    library = library_trees(bots_dir)
    everyone = distance_fn(app_dir, trees, {**library, **trees}) if trees else {}
    result = {"library": {c: {b: d for b, d in row.items() if b in library}
                          for c, row in everyone.items()},
              "classes": {c: {o: d for o, d in row.items() if o in trees and o != c}
                          for c, row in everyone.items()}}
    (run_dir / "distances.json").write_text(json.dumps(result, indent=2), encoding="utf-8")
    return result
