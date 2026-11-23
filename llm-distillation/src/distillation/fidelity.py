"""How well a model's stated programs match the way it plays, opponent by opponent.

* Stated: the programs the model writes (``distillation-stated``), weighted by sample count.
* Revealed: the model's own C/D replies when shown each library bot (``distillation-llm``).

For opponent ``o``, ``p(o)`` is the revealed C-rate and ``s(o)`` the C-rate of the stated
programs with a proved action against ``o`` (open cells are left out); ``s(o)`` is ``None``
when no program has one. The fidelity error ``eps`` is the mean of ``|p(o) - s(o)|`` over the
opponents where ``s(o)`` exists.
"""

from __future__ import annotations

import json
import math
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

@dataclass(frozen=True)
class Fidelity:
    plays: dict[str, float]
    """The model's C-rate against each opponent with data in both runs (revealed play)."""

    states: dict[str, float | None]
    """The C-rate of the stated programs with a proved action against each opponent. None if no program has one."""

    proved: dict[str, int]
    """How many stated programs have a proved action against each opponent."""

    n_programs: int
    """How many valid stated programs there are."""

    eps: float | None
    """The mean of ``|plays - states|`` over the opponents whose ``states`` is not None. None if there are none."""

    confident: tuple[float, float] | None
    """The interval that contains the true ``eps`` with probability ``1 - delta``."""

    delta: float
    """The failure probability of the confidence interval."""

def _read(run_dir: Path, name: str):
    """Read the JSON run file."""

    return json.loads((run_dir / name).read_text(encoding="utf-8"))

def load_stated(run_dir: Path) -> dict[str, Counter]:
    """Per opponent, how many valid stated programs play ``C``, ``D`` or are ``open``."""

    counts: dict[str, Counter] = {}
    for bot in _read(run_dir, "bots.json"):
        if bot["valid"]:
            for cell in bot["cells"]:
                action = cell["my_action"] if cell["verdict"] == "stable" else "open"
                counts.setdefault(cell["opponent"], Counter())[action] += bot.get("count", 1)
    return counts

def load_revealed(run_dir: Path) -> dict[str, Counter]:
    """Per opponent, the model's ``C`` and ``D`` replies; unparsed replies are dropped."""

    return {opponent: Counter(r["action"] for r in replies if r["action"] in ("C", "D"))
            for opponent, replies in _read(run_dir, "raw_responses.json").items()}

def confidence_radius(n_programs: int, proved: list[int], replies: list[int],
                      delta: float) -> float:
    """Confidence radius for ``eps`` over ``N`` opponents.

    One stated program moves ``s(o)`` by at most ``1 / proved(o)``, so ``eps`` by at most
    ``mean_o 1 / proved(o)``; one reply against ``o`` moves ``eps`` by at most
    ``1 / (N * replies(o))``.
    """

    n = len(proved)
    per_program = sum(1 / v for v in proved) / n
    squared = n_programs * per_program ** 2 + sum(1 / (n * n * r) for r in replies)
    return math.sqrt(squared * math.log(2 / delta) / 2)

def compare(stated: dict[str, Counter], revealed: dict[str, Counter],
            delta: float = 0.05) -> Fidelity:
    """Compare the stated programs to the revealed play, opponent by opponent."""

    opponents = [o for o in stated if stated[o].total() and revealed.get(o, Counter()).total()]
    if not opponents:
        raise ValueError("no opponent has data in both runs")

    plays = {o: revealed[o]["C"] / revealed[o].total() for o in opponents}
    proved = {o: stated[o]["C"] + stated[o]["D"] for o in opponents}
    states = {o: stated[o]["C"] / proved[o] if proved[o] else None for o in opponents}

    scored = [o for o in opponents if states[o] is not None]
    eps = confident = None
    if scored:
        eps = sum(abs(plays[o] - states[o]) for o in scored) / len(scored)
        radius = confidence_radius(stated[scored[0]].total(), [proved[o] for o in scored],
                                   [revealed[o].total() for o in scored], delta)
        confident = (max(0.0, eps - radius), min(1.0, eps + radius))

    return Fidelity(plays=plays, states=states, proved=proved,
                    n_programs=stated[opponents[0]].total(),
                    eps=eps, confident=confident, delta=delta)

def check_same_model(stated_dir: Path, revealed_dir: Path) -> str:
    """Check that the two runs are of the same model and return its name."""

    models = {_read(d, "metadata.json")["model"] for d in (stated_dir, revealed_dir)}
    if len(models) != 1:
        raise ValueError(f"the runs are of different models: {sorted(models)}")
    return models.pop()

def format_report(model: str, result: Fidelity) -> str:
    """Text report of the fidelity comparison."""
    
    lines = [f"Fidelity of {model}",
             f"{'opponent':<15}{'plays C':>9}{'states C':>10}{'error':>8}{'proved':>9}"]
    for o, p in result.plays.items():
        s = result.states[o]
        states, err = ("open", "open") if s is None else (f"{s:.2f}", f"{abs(p - s):.2f}")
        lines.append(f"{o:<15}{p:>9.2f}{states:>10}{err:>8}"
                     f"{f'{result.proved[o]}/{result.n_programs}':>9}")

    scored = sum(s is not None for s in result.states.values())
    if result.eps is None:
        lines += ["", "eps  open (no opponent has a proved stated program)"]
    else:
        low, high = result.confident
        lines += ["", f"eps  {result.eps:.3f} over {scored} of {len(result.plays)} opponents",
                  f"     {1 - result.delta:.0%} confidence {low:.3f}-{high:.3f}"]
    return "\n".join(lines)
