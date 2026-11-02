"""Turn judged + profiled samples into a stated profile, fits, and a report.

Two aggregation orders, both reported (they answer different questions):

* **Average then fit** -- ``x̄_j`` = fraction of samples (with a determined cell
  against opponent ``j``) that cooperate with ``j``; fit ``x̄`` with every metric.
  For squared L2 and ExpectedHamming this is exactly "the one zoo mixture that
  minimises the AVERAGE per-sample loss" (``Σ_i‖Rᵀw−x_i‖² = m‖Rᵀw−x̄‖² + const``).
* **Fit then average** -- fit each COMPLETE sample profile (L2) and average the
  weights: a distribution over zoo TYPES ("40% of self-reports are DupocBot-like").

Undetermined and non-terminating cells are MISSING DATA: excluded from both the
numerator and the denominator of ``x̄_j`` and reported as coverage. They are never
imputed (in particular never read as ``D``). Opponents with zero coverage are
dropped from the fit (the fit runs on the remaining columns of ``R``).
"""

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass

import numpy as np

from ..data import ReferenceLibrary
from ..fitting import fit_all, fit_binomial, fit_l2
from ..reporting import format_report
from .evaluate import NONTERMINATING, Cell
from .parse import Sample
from .prog import show
from .zoo import zoo_names


@dataclass
class Aggregate:
    opponents: tuple[str, ...]
    c: np.ndarray            # cooperations per opponent
    n: np.ndarray            # determined (C or D) samples per opponent
    undetermined: np.ndarray
    nonterminating: np.ndarray
    n_valid: int
    n_total: int

    @property
    def x(self) -> np.ndarray:
        return np.divide(self.c, self.n, out=np.full_like(self.c, np.nan),
                         where=self.n > 0)

    @property
    def covered(self) -> np.ndarray:
        return self.n > 0


def aggregate(library: ReferenceLibrary, samples: list[Sample],
              profiles: dict[int, dict[str, Cell]]) -> Aggregate:
    m = library.n
    c, n, u, nt = (np.zeros(m) for _ in range(4))
    for s in samples:
        if not s.valid:
            continue
        for j, opp in enumerate(library.bots):
            v = profiles[s.index][opp].value
            if v in ("C", "D"):
                n[j] += 1
                c[j] += v == "C"
            elif v == NONTERMINATING:
                nt[j] += 1
            else:
                u[j] += 1
    return Aggregate(library.bots, c, n, u, nt,
                     n_valid=sum(s.valid for s in samples), n_total=len(samples))


def type_distribution(library: ReferenceLibrary, samples: list[Sample],
                      profiles: dict[int, dict[str, Cell]], cols: np.ndarray):
    """Fit-then-average: mean L2 weight vector over COMPLETE sample profiles."""
    R = library.R[:, cols]
    opps = [b for b, keep in zip(library.bots, cols) if keep]
    weights, used = [], 0
    for s in samples:
        if not s.valid:
            continue
        vals = [profiles[s.index][o].value for o in opps]
        if any(v not in ("C", "D") for v in vals):
            continue
        x = np.array([1.0 if v == "C" else 0.0 for v in vals])
        weights.append(fit_l2(R, x).weights)
        used += 1
    if not weights:
        return None, 0
    return np.mean(weights, axis=0), used


def signature(cells: dict[str, Cell], opponents) -> str:
    """Compact behaviour string, one char per opponent: C, D, N, or ? (undetermined)."""
    return "".join(cells[o].value or "?" for o in opponents)


def build_report(library: ReferenceLibrary, samples: list[Sample],
                 profiles: dict[int, dict[str, Cell]],
                 revealed: dict[str, float] | None = None) -> tuple[str, Aggregate]:
    agg = aggregate(library, samples, profiles)
    bots = library.bots
    w = max(len(b) for b in bots)
    out: list[str] = []

    # -- validity
    out.append("=== Samples ===")
    out.append(f"valid programs: {agg.n_valid}/{agg.n_total}")
    errors = Counter(e.split(":")[0] for s in samples if not s.valid for e in s.errors)
    for e, k in errors.most_common():
        out.append(f"  invalid — {e}: {k}")
    warn = Counter(wn.split(":")[0] for s in samples if s.valid for wn in s.warnings)
    for wn, k in warn.most_common():
        out.append(f"  warning — {wn}: {k}")
    out.append("")

    # -- behaviour clusters
    out.append("=== Behaviour clusters (one char per opponent, library order) ===")
    out.append("  opponents: " + " ".join(bots))
    clusters: dict[str, list[Sample]] = defaultdict(list)
    for s in samples:
        if s.valid:
            clusters[signature(profiles[s.index], bots)].append(s)
    for sig, members in sorted(clusters.items(), key=lambda kv: -len(kv[1])):
        rep = members[0]
        ident = {c.reason for c in profiles[rep.index].values() if c.reason.startswith("syntactically")}
        tag = f"  [{ident.pop()}]" if ident else ""
        distinct = len({show(m.program) for m in members})
        out.append(f"  {sig}  ×{len(members)}  ({distinct} distinct source(s)){tag}")
        out.append(f"      e.g. #{rep.index}: {show(rep.program, zoo_names())}")
    out.append("")

    # -- coverage + the stated vector
    out.append("=== Stated profile x̄ (average over determined cells) ===")
    out.append(f"  {'opponent'.ljust(w)}   x̄      C/n    undet  nonterm")
    for j, b in enumerate(bots):
        xs = f"{agg.x[j]:.3f}" if agg.covered[j] else "  —  "
        out.append(f"  {b.ljust(w)}  {xs}  {int(agg.c[j]):>3}/{int(agg.n[j]):<3}"
                   f"  {int(agg.undetermined[j]):>5}  {int(agg.nonterminating[j]):>7}")
    out.append("  (undetermined = needs a proof the Python evaluator cannot certify; "
               "never imputed)")
    out.append("")

    cols = agg.covered
    if not cols.any():
        out.append("No opponent has a determined cell: nothing to fit.")
        return "\n".join(out) + "\n", agg
    opps = tuple(b for b, keep in zip(bots, cols) if keep)
    if not cols.all():
        out.append(f"Fits use the {cols.sum()} covered opponent column(s) only; "
                   f"dropped: {', '.join(b for b, k in zip(bots, cols) if not k)}.")
        out.append("")

    # -- average then fit
    R, x = library.R[:, cols], agg.x[cols]
    fits = fit_all(R, x) + [fit_binomial(R, agg.c[cols], agg.n[cols])]
    out.append("##### Average-then-fit (x̄ against the zoo hull) #####")
    out.append(format_report(library, fits, x, opps))

    # -- fit then average
    out.append("##### Fit-then-average (L2 per complete sample, weights averaged) #####")
    wbar, used = type_distribution(library, samples, profiles, cols)
    if wbar is None:
        out.append("  no sample has a complete profile on the covered opponents")
    else:
        out.append(f"  over {used} complete sample profile(s):")
        for i in np.argsort(-wbar):
            if wbar[i] > 1e-6:
                out.append(f"  {bots[i].ljust(w)}  {wbar[i]:.4f}")
    out.append("")

    # -- stated vs revealed
    if revealed is not None:
        out.append("##### Stated (written programs) vs revealed (played games) #####")
        out.append(f"  {'opponent'.ljust(w)}  stated  revealed   diff")
        for j, b in enumerate(bots):
            r = revealed.get(b)
            st = agg.x[j] if agg.covered[j] else None
            if st is None or r is None:
                out.append(f"  {b.ljust(w)}  {'—' if st is None else f'{st:.3f}':>6}  "
                           f"{'—' if r is None else f'{r:.3f}':>8}")
            else:
                out.append(f"  {b.ljust(w)}  {st:6.3f}  {r:8.3f}  {st - r:+6.3f}")
        out.append("")

    return "\n".join(out).rstrip() + "\n", agg
