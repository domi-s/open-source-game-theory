"""Approach 3: the LLM writes its own strategy as a ``Prog`` program.

Separate from the revealed-strategy pipeline (``distillation.pipeline``): that one
PLAYS the model against each library bot; this one asks the model to WRITE its
policy as source code, profiles the written programs, and fits the average.
Entry point: ``distillation-stated`` (``stated/cli.py``).
"""
