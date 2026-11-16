"""Tree edit distances between programs. Runs in the APP's environment.

Not imported by the distillation package: ``neighbours.py`` invokes it as

    uv run --directory <app> python <this file>

with ``{"programs": {id: tree}, "library": {name: tree}}`` on stdin (trees are nested
``[label, [children...]]``, see ``tree.py``) and reads ``{id: {name: distance}}`` from
stdout. The distance is the app's own Zhang-Shasha ``tree_edit_distance`` (unit costs), so
there is one implementation of it; only the trees differ (this package's are lossless).
"""

from __future__ import annotations

import json
import sys

from pd_runner.tau.syntax import Node, tree_edit_distance


def _node(tree) -> Node:
    return Node(tree[0], tuple(_node(c) for c in tree[1]))


def main() -> int:
    request = json.load(sys.stdin)
    library = {name: _node(t) for name, t in request["library"].items()}
    print(json.dumps({
        pid: {name: tree_edit_distance(_node(t), lib) for name, lib in library.items()}
        for pid, t in request["programs"].items()}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
