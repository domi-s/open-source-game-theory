import json
import sys
from pathlib import Path

import numpy as np

from distillation.data import load_library
from distillation.fitting import fit_all, fit_binomial
from distillation.reporting import format_report

run = Path(sys.argv[1])
library = load_library("data/payoff_matrix.csv")
raw = json.loads((run / "raw_responses.json").read_text())

c = np.array([sum(r["action"] == "C" for r in raw[b]) for b in library.bots], dtype=float)
n = np.array([sum(r["action"] in ("C", "D") for r in raw[b]) for b in library.bots], dtype=float)
x = c / n

for bot, ci, ni in zip(library.bots, c, n):
    print(f"{bot}: {int(ci)}/{int(ni)}")
print()

fits = fit_all(library.R, x) + [fit_binomial(library.R, c, n)]
print(format_report(library, fits, x))