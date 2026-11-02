"""The stated-strategy prompt: the Prog spec plus "write the bot that is you"."""

from __future__ import annotations

from pathlib import Path

from ..bot_descriptions import BOT_DESCRIPTIONS

# repo/engine/... relative to repo/llm-distillation/src/distillation/stated/prompt.py
DEFAULT_SPEC_PATH = (Path(__file__).resolve().parents[4]
                     / "engine/PrisonersDilemma/Research/Notes/PROG_LANGUAGE_SPEC.md")

MAIN_NAME = "MyBot"

TASK = f"""\
You will play a one-shot Prisoner's Dilemma under *maximum transparency*: before
anyone moves, your opponent's full source code is visible to you, and your source
code is visible to your opponent. Payoffs (you, opponent): both C -> (3, 3);
you C / they D -> (0, 5); you D / they C -> (5, 0); both D -> (1, 1).

Your task is to write YOUR OWN strategy for this game as a program in the `Prog`
language specified below. The program must play exactly the way you would play,
against ANY opponent whose source code you can read -- not just against the bots
mentioned in the specification. It is your policy, written down as source code.

Requirements:
  - Write it in Lean 4 using only the `Prog` constructors from the specification
    (`.const .self .opp .bot .sim .ite .search` and the `Formula` constructors
    `.plays .impl .neg .box .eq`). Do not use `.tvote`, `.sys`, `.selfIdx` or
    `.diag`.
  - Name the bot `{MAIN_NAME}`. If it uses `.search`, it must take its budget as a
    parameter: `def {MAIN_NAME} (k : Nat) : Prog := ...`. You may reference the zoo
    bots from the specification by name (e.g. `.bot (DupocBot k)`) and you may
    define helper bots with `def` before `{MAIN_NAME}`.
  - Reason as much as you like, then give your final answer as exactly one
    ```lean code block containing `def {MAIN_NAME}`. Only the last such block counts.
"""

ZOO_HINT = """\
For context, here are some of the opponents you may face, in pseudocode (the same
bots exist under these names in the language; see the specification):
"""


def build_stated_prompt(spec_text: str, show_zoo: bool = False) -> str:
    parts = [TASK, "", "# The Prog language specification", "", spec_text.strip()]
    if show_zoo:
        parts += ["", "# Opponents", "", ZOO_HINT]
        for name, code in BOT_DESCRIPTIONS.items():
            parts += [f"## {name}", "```python", code.rstrip(), "```", ""]
    return "\n".join(parts).rstrip() + "\n"
