"""Canonical form of a stated bot's Lean source.

``canonicalise`` normalises a bot's source code so that two programs that are the same up to: comments, whitespace, import order, bot name, budget-parameter names and layout

Anything that does not parse as a ``def <name> (k … : Nat) … : Prog`` header is left
un-renamed rather than guessed at (still comment-stripped and tidied).
"""

from __future__ import annotations

import re

DEFAULT_NAME = "StatedBot"
"""The default name for a canonical bot."""

_IDENT_RE = re.compile(r"(?<![\w.'])[A-Za-z_][\w']*")
"""An identifier is a letter or underscore followed by letters, digits, underscores or apostrophes, not preceded by a letter, digit, underscore, dot or apostrophe."""

_HEADER_RE = re.compile(
    r"(?P<head>^[ \t]*def[ \t]+)(?P<name>[A-Za-z_][\w']*)"
    r"(?P<binders>(?:\s*\([^()]*\))*)\s*:\s*Prog\b",
    re.MULTILINE)
"""A bot's header is a ``def <name> (k … : Nat) … : Prog`` line, possibly with whitespace and comments before it. The binders are captured for renaming."""

_BINDER_RE = re.compile(r"\(\s*([\w'\s]+?)\s*:\s*Nat\s*\)")
"""A binder is a parenthesised list of identifiers, each with type ``Nat``. The identifiers are captured for renaming."""

_LAYOUT_KEYWORDS = {"let", "have", "show", "do", "match", "where", "by", "calc",
                    "suffices", "nomatch"}
"""These keywords introduce a new layout block, so whitespace between tokens is meaningful and the body should not be collapsed to one line."""

_ACTION_SHORTHAND_RE = re.compile(r"(?<![\w.')\]])\.([CD])(?![\w'])")
"""``.C`` / ``.D`` as written without the ``Action`` prefix. Every position that takes an action elaborates both spellings to the same term, so they are rewritten to ``Action.C`` / ``Action.D``. (Not matched: ``x.C`` field access, ``Action.C`` itself, ``.DefectBot``.)"""


def strip_comments(text: str) -> str:
    """Remove Lean comments; caution around string literals."""

    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1
                i += 2
            elif two == "-/":
                depth -= 1
                i += 2
                if depth == 0:
                    out.append(" ")
            else:
                i += 1
        elif two == "/-":
            depth = 1
            i += 2
        elif two == "--":
            while i < n and text[i] != "\n":
                i += 1
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def _rename_identifiers(text: str, mapping: dict[str, str]) -> str:
    """Rename identifiers all at once, so swaps like k1<->k2 cannot collide."""

    return _IDENT_RE.sub(lambda m: mapping.get(m.group(0), m.group(0)), text)


def _tidy(text: str) -> str:
    """Remove empty lines and sort the imports to a canonical order."""

    lines = [ln.rstrip() for ln in text.splitlines()]
    lines = [ln for ln in lines if ln.strip()]
    imports = sorted(ln for ln in lines if ln.startswith("import "))
    rest = [ln for ln in lines if not ln.startswith("import ")]
    return "\n".join(imports + rest) + "\n"


def _collapse_layout(text: str) -> str:
    """Put the def's body on one line when no construct makes newlines meaningful.

    Without ``let``/``have``/``do``/``match``/``where``/``by``..., whitespace between
    tokens carries no meaning, so ``(.search k\\n  (.plays`` and the one-line spelling
    are the same program. The trailing ``end <namespace>`` stays on its own line.
    """

    m = _HEADER_RE.search(text)
    if not m:
        return text
    tail = re.search(r"^end\b.*\Z", text[m.end():], re.MULTILINE | re.DOTALL)
    cut = m.end() + (tail.start() if tail else len(text) - m.end())
    body = text[m.end():cut]
    if set(_IDENT_RE.findall(body)) & _LAYOUT_KEYWORDS:
        return text
    body = re.sub(r"\s+", " ", body).replace("( ", "(").replace(" )", ")").rstrip()
    return text[:m.end()] + body + "\n" + text[cut:]


def _rename_budgets(text: str) -> str:
    """Rename the budget parameters to k1, k2, … in order of first use."""

    m = _HEADER_RE.search(text)
    if not m:
        return text
    groups = _BINDER_RE.findall(m.group("binders"))
    binders = m.group("binders")
    if not groups or _BINDER_RE.sub("", binders).strip():
        return text
    params = [p for g in groups for p in g.split()]
    if len(set(params)) != len(params):
        return text
    body = text[m.end():]
    first_use = [t for t in dict.fromkeys(_IDENT_RE.findall(body)) if t in params]
    order = first_use + [p for p in params if p not in first_use]
    mapping = {p: f"k{i + 1}" for i, p in enumerate(order)}
    others = set(_IDENT_RE.findall(body)) - set(params)
    if others & set(mapping.values()):
        return text  # a `k1` already means something else in the body
    header = f"{m.group('head')}{m.group('name')} ({' '.join(mapping.values())} : Nat) : Prog"
    return text[:m.start()] + header + _rename_identifiers(body, mapping)


def canonicalise(source: str, name: str = DEFAULT_NAME) -> str:
    """Canonical text of ``source`` with the bot named ``name`` (see module docstring)."""
    
    text = _ACTION_SHORTHAND_RE.sub(r"Action.\1", strip_comments(source))
    text = _tidy(text)
    m = _HEADER_RE.search(text)
    if m:
        text = _rename_identifiers(text, {m.group("name"): name})
    return _collapse_layout(_rename_budgets(text))
