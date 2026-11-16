"""A LOSSLESS tree of a canonical ``Prog`` program, for edit distance to library bots.

Unlike ``app/.../tau/syntax.py`` (a confusability metric for the tau layer), nothing is
erased: actions (``action:C``), budget expressions (``nat:2*k+64``) and bot references
(``ref:DefectBot``) are all labelled nodes, so distance 0 means the same program and a
polarity flip or a changed budget is a real edit.

Input is ``canonical.program_key`` output (one def, comments gone, ``.C`` spelled
``Action.C``). Anything outside the plain ``Prog`` grammar (``let``, ``.tvote``, ``.sys``,
helper defs) gives ``None`` rather than a partial tree.
"""

from __future__ import annotations

import re

from .canonical import _HEADER_RE

Tree = tuple[str, tuple]  # (label, children)

_ARITY = {".const": 1, ".self": 0, ".opp": 0, ".bot": 1, ".sim": 2, ".ite": 4, ".search": 4,
          ".plays": 3, ".impl": 2, ".neg": 1, ".box": 2, ".eq": 2, ".diag": 2}
_TOKEN_RE = re.compile(r"[()]|[^\s()]+")
_BOT_NAME_RE = re.compile(r"[A-Z]\w*")


def program_tree(program: str) -> Tree | None:
    """The tree of ``program``'s body, or None if it is not plain ``Prog``."""
    m = _HEADER_RE.search(program)
    body = program[m.end():].lstrip() if m else ""
    if not body.startswith(":="):
        return None
    tokens, pos = _TOKEN_RE.findall(body[2:]), 0

    def take() -> str:
        nonlocal pos
        pos += 1
        return tokens[pos - 1]

    def term() -> Tree:
        tok = take()
        if tok == "(":
            head = tokens[pos]
            if head == "(" or head.startswith("Action."):
                node = term()
            elif head in _ARITY:
                node = application(take())
            elif _BOT_NAME_RE.fullmatch(head):  # `(CupodBot k)`: a reference with arguments
                name, args = take(), []
                while tokens[pos] != ")":
                    args.append(term())
                node = (f"ref:{name}", tuple(args))
            else:  # a budget expression such as `(2 * k + 64)`
                depth, parts = 1, []
                while depth:
                    t = take()
                    depth += (t == "(") - (t == ")")
                    parts.append(t)
                return (f"nat:{''.join(parts[:-1])}", ())
            if take() != ")":
                raise ValueError("expected ')'")
            return node
        if tok in _ARITY:
            return application(tok)
        if tok.startswith("Action."):
            return (f"action:{tok[-1]}", ())
        if _BOT_NAME_RE.fullmatch(tok):
            return (f"ref:{tok}", ())
        if tok == ")":
            raise ValueError("unexpected ')'")
        return (f"nat:{tok}", ())

    def application(head: str) -> Tree:
        return (head[1:], tuple(term() for _ in range(_ARITY[head])))

    try:
        tree = term()
    except (IndexError, ValueError):
        return None
    return tree if pos == len(tokens) else None


def tree_size(tree: Tree) -> int:
    return 1 + sum(tree_size(c) for c in tree[1])
