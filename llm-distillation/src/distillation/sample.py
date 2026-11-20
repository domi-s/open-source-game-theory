"""Step 1: Sample. Ask the model for a bot n times -> keep the raw replies and the programs"""

from __future__ import annotations

import json
import os
import re
from pathlib import Path

from .openrouter import make_client
from .pipeline import API_KEY_ENV
from .progress import Progress

PROMPT_TEMPLATE = """\
You are playing a one-shot Prisoner's Dilemma under *maximum transparency*: your
opponent can read your full source code and you can read theirs.

Write your own strategy for this game as a bot in the `Prog` language specified
below: the program that plays exactly as you would against any opponent. Name it
`MyBot`. Follow the output contract in section 12 of the specification (a complete
Lean file: imports, `namespace PD.Bots`, the definition, `end PD.Bots`).

Reason as much as you like, then give your final answer as one ```lean code block.

{spec}
"""

_LEAN_BLOCK_RE = re.compile(r"```lean4?\s*\n(.*?)```", re.DOTALL)
"""Regular expression to find lean code blocks."""

def extract_bot(text: str, name: str = "MyBot") -> str | None:
    """Optional of the last ```lean block, with ``MyBot`` renamed to ``name``."""
    blocks = _LEAN_BLOCK_RE.findall(text)
    if not blocks or not re.search(r"\bdef\s+MyBot\b", blocks[-1]):
        return None
    return re.sub(r"\bMyBot\b", name, blocks[-1])

def sample(run_dir: Path, model: str, n: int, temperature: float, spec_path: Path) -> None:
    """Query the model ``n`` times, saving ``raw_responses.json`` after each reply."""
    prompt = PROMPT_TEMPLATE.format(spec=spec_path.read_text(encoding="utf-8"))
    api_key = os.environ.get(API_KEY_ENV)
    if not api_key:
        raise RuntimeError(f"Environment variable {API_KEY_ENV} is not set.")
    client = make_client(api_key)

    responses = []
    progress = Progress(1, n)
    for i in range(n):
        progress.show(0, "sampling", i)
        reply = client.chat.completions.create(
            model=model, messages=[{"role": "user", "content": prompt}],
            temperature=temperature)
        responses.append({"index": i, "raw": reply.choices[0].message.content or ""})
        (run_dir / "raw_responses.json").write_text(json.dumps(responses, indent=2),
                                                    encoding="utf-8")
        progress.done += 1
    progress.clear()

def extract_programs(run_dir: Path) -> list[dict]:
    """Write ``programs.json``: each reply's program (None if it wrote none)."""
    responses = json.loads((run_dir / "raw_responses.json").read_text(encoding="utf-8"))
    programs = [{"index": r["index"], "program": extract_bot(r["raw"])} for r in responses]
    (run_dir / "programs.json").write_text(json.dumps(programs, indent=2), encoding="utf-8")
    return programs
