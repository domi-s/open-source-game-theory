# Stated pipeline: steps

Each step is its own module, reads the previous step's file and writes its own, all in the run folder.

| # | Step (`--only`) | Module | Writes | What it does |
|---|---|---|---|---|
| 1 | `sample` | `sample.py` | `raw_responses.json`, `programs.json` | Ask the model for a bot `n` times; extract each reply's program. |
| 2 | `canonicalise` | `classes.py` | `classes.json` | Group programs equal up to comments, name, budget parameters and layout. Class size = weight. |
| 3a | `distances` | `distances.py` | `distances.json` | Tree edit distance from each class to every library bot and every other class. |
| 3b/4 | `outcomes` | `stated.py` | `bots.json`, `cooperation_vector.json`, `report.txt` | Each class's action against each library bot (theorem, else Lean eval, else open), then the fit. |

```
distillation-stated --model <openrouter id> --n 30            # all steps, new run
distillation-stated --model <id> --only sample                # just step 1
distillation-stated --from-run runs/<folder>                  # all steps, resuming
distillation-stated --from-run runs/<folder> --only distances
distillation-stated --from-run runs/<folder> --from-step outcomes
```

Steps 1, 2 and 3a need no Lean. A full pass skips `distances.json` if it exists; `--only distances` redoes it.
