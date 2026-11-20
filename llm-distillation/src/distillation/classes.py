"""Step 2. Canonicalise / Classes. Group samples that wrote the same program -> the group size is its weight."""

from __future__ import annotations

import json
from pathlib import Path

from .canonical import DEFAULT_NAME, budget_params, canonicalise

def group_samples(programs: list[dict]) -> list[dict]:
    """One class per canonical program (see ``canonical.py``), in first-seen order.

    A class is named after its first sample and carries ``indices``/``count`` (its
    weight). Samples with no usable bot form one class whose ``source`` is None.
    """
    classes: dict[str | None, dict] = {}
    for p in programs:
        raw = p["program"]
        key = canonicalise(raw, DEFAULT_NAME) if raw is not None else None
        if key not in classes:
            name = f"StatedBot{p['index']}"
            classes[key] = {"index": p["index"], "name": name, "indices": [], "count": 0,
                            "budget_params": 0 if raw is None else budget_params(raw),
                            "source": None if raw is None else canonicalise(raw, name)}
        classes[key]["indices"].append(p["index"])
        classes[key]["count"] += 1
    return list(classes.values())

def canonicalise_programs(run_dir: Path) -> list[dict]:
    """Write ``classes.json`` from ``programs.json``."""
    programs = json.loads((run_dir / "programs.json").read_text(encoding="utf-8"))
    classes = group_samples(programs)
    (run_dir / "classes.json").write_text(json.dumps(classes, indent=2), encoding="utf-8")
    return classes
