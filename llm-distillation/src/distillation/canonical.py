"""Canonical form of a stated bot's Lean source.

``canonicalise`` normalises a bot's source code so that two programs that are the same up to: comments, whitespace, import order, bot name, layout, and the names and NUMBER of budget parameters (all are one shared ``k``, see ``_rename_budgets``)

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

_QUALIFIED_CONSTRUCTOR_RE = re.compile(
    r"(?<![\w.'])(?:PD\.)?(?:Prog\.(const|self|opp|bot|sim|ite|search|tvote|sys|selfIdx)"
    r"|Formula\.(plays|impl|neg|box|eq|diag))(?![\w'])")
"""``Prog.search`` / ``Formula.plays`` as written instead of ``.search`` / ``.plays``; rewritten to the dot form, which elaborates to the same constructor. (``nil``/``cons`` are left alone: two list types share them.)"""

_NEXT_COMMAND_RE = re.compile(r"^(?:def|end|namespace|section|theorem|lemma|open|instance)\b",
                              re.MULTILINE)
"""The start of the next top-level command, which ends a def's text."""


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


def _budget_params(header: re.Match) -> list[str] | None:
    """The budget parameter names of a def header; None if a binder is not a plain ``Nat``."""

    binders = header.group("binders")
    if _BINDER_RE.sub("", binders).strip():
        return None
    return [p for g in _BINDER_RE.findall(binders) for p in g.split()]


def budget_params(source: str) -> int:
    """How many free budget parameters the bot was written with (0 if none or unparsed)."""

    m = _HEADER_RE.search(strip_comments(source))
    return len(_budget_params(m) or []) if m else 0


def _rename_budgets(text: str) -> str:
    """THE BUDGET RULE: every budget parameter is the same shared ``k``.

    The evaluator instantiates every parameter of a bot with one ``k`` (as do the
    library's proved cells: ``PrudentBot k`` / ``OptimBot k k``), so ``(kOut kIn)`` is
    ``(k)`` with both uses renamed: ``PrudentBot2 k k`` IS ``PrudentBot k``. Staggering
    through the parameters is therefore collapsed; staggering written into the program
    (``.search (2 * k + 64) …``) is the program's own and is kept.
    """

    m = _HEADER_RE.search(text)
    params = _budget_params(m) if m else None
    if not params or len(set(params)) != len(params):
        return text
    body = text[m.end():]
    if "k" in set(_IDENT_RE.findall(body)) - set(params):
        return text  # a `k` already means something else in the body
    header = f"{m.group('head')}{m.group('name')} (k : Nat) : Prog"
    return text[:m.start()] + header + _rename_identifiers(body, dict.fromkeys(params, "k"))


def canonicalise(source: str, name: str = DEFAULT_NAME) -> str:
    """Canonical text of ``source`` with the bot named ``name`` (see module docstring)."""
    
    text = _ACTION_SHORTHAND_RE.sub(r"Action.\1", strip_comments(source))
    text = _QUALIFIED_CONSTRUCTOR_RE.sub(r".\1\2", text)
    text = _tidy(text)
    m = _HEADER_RE.search(text)
    if m:
        text = _rename_identifiers(text, {m.group("name"): name})
    return _collapse_layout(_rename_budgets(text))


def program_key(source: str, name: str | None = None) -> str | None:
    """Canonical text of ONE bot definition in ``source``; equal keys mean the same program.

    Picks ``def <name> … : Prog`` (the first ``: Prog`` def if ``name`` is None), cuts it
    at the next top-level command, and canonicalises just that, so the imports, the
    namespace and any other definitions in the file do not matter. Budget expressions,
    bot references and actions are all kept, so unlike a lossy tree metric, equality here
    is genuine identity of the program (and hence of its outcomes). ``None`` if no such
    definition exists.
    """
    text = strip_comments(source)
    for m in _HEADER_RE.finditer(text):
        if name is not None and m.group("name") != name:
            continue
        nxt = _NEXT_COMMAND_RE.search(text, m.end())
        return canonicalise(text[m.start():nxt.start() if nxt else len(text)])
    return None
