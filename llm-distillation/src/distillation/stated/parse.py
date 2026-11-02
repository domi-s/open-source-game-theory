"""Parse LLM-written Lean bot definitions into the Python ``Prog`` mirror.

Scope (v0): the term language of ordinary bots, exactly as the engine and the
spec (``PROG_LANGUAGE_SPEC.md``) write it --

    def Name (k : Nat) : Prog :=
      [let x : Prog := <prog>]*
      <prog>

with ``.const .self .opp .bot .sim .ite .search`` and formulas
``.plays .impl .neg .box .eq``; named bot references (``DupocBot k``,
``.bot TitForTatBot``, ``Bots.CupodBot k``) to the zoo or to earlier ``def``s in
the same file. Anything else -- ``match``, ``if``, ``fun``, ``.tvote``, ``.sys``,
``.diag`` -- is a :class:`ParseError`, i.e. an INVALID sample.

The parser is ARITY-DIRECTED: every constructor and every named definition has a
fixed number of arguments, so it consumes exactly that many and layout/newlines
never matter (which is also why ``let`` needs no layout rule).

Named references are INLINED (a Lean ``def`` is transparent: ``CupodBot k`` *is*
its body). That is what makes ``==`` on the result syntactic identity in the
sense of Lean's ``.eq``.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from .prog import (
    Bot, Box, Const, Eq, Impl, Ite, Neg, Opp, Plays, Prog, Search, Self, Sim,
    has_search, rename_budgets,
)

PROG_CTORS = {"const", "self", "opp", "bot", "sim", "ite", "search"}
FORMULA_CTORS = {"plays", "impl", "neg", "box", "eq"}
UNSUPPORTED = {"tvote", "sys", "selfIdx", "diag"}


class ParseError(ValueError):
    pass


@dataclass(frozen=True)
class Definition:
    """A parsed ``def``: parameter names and the (closed-over-names) body."""

    name: str
    params: tuple[str, ...]
    body: Prog


@dataclass
class ParsedFile:
    defs: dict[str, Definition]
    order: list[str]
    warnings: list[str] = field(default_factory=list)


# ------------------------------------------------------------------- tokenizer
def strip_comments(src: str) -> str:
    """Remove ``--`` line comments and (nested) ``/- … -/`` block comments."""
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and src.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


_TOKEN_RE = re.compile(r":=|[()\[\]{},:;+*\-/^]|\.?[A-Za-z_][\w'.]*|\d+|\S")


def tokenize(src: str) -> list[str]:
    return _TOKEN_RE.findall(strip_comments(src))


def _ctor(tok: str, family: set[str]) -> str | None:
    """``.sim`` / ``Prog.sim`` / ``PD.Prog.sim`` → ``"sim"`` (or None)."""
    for prefix in (".", "Prog.", "PD.Prog.", "Formula.", "PD.Formula."):
        if tok.startswith(prefix) and tok[len(prefix):] in family:
            return tok[len(prefix):]
    return None


def _bare_name(tok: str) -> str:
    for prefix in ("PD.Bots.", "Bots.", "PD."):
        if tok.startswith(prefix):
            return tok[len(prefix):]
    return tok


# ---------------------------------------------------------------------- parser
class _Parser:
    def __init__(self, tokens: list[str], scope: dict[str, Definition],
                 params: tuple[str, ...], warnings: list[str]):
        self.toks, self.i = tokens, 0
        self.scope = scope          # named definitions visible here
        self.params = set(params)   # this def's Nat parameters
        self.lets: dict[str, Prog] = {}
        self.warnings = warnings

    # -- token helpers
    def peek(self) -> str | None:
        return self.toks[self.i] if self.i < len(self.toks) else None

    def next(self) -> str:
        tok = self.peek()
        if tok is None:
            raise ParseError("unexpected end of input")
        self.i += 1
        return tok

    def expect(self, tok: str) -> None:
        got = self.next()
        if got != tok:
            raise ParseError(f"expected {tok!r}, got {got!r}")

    # -- atoms
    def action(self) -> str:
        tok = self.next()
        if tok == "(":
            a = self.action()
            self.expect(")")
            return a
        for form in ("Action.", "PD.Action.", "."):
            if tok.startswith(form) and tok[len(form):] in ("C", "D"):
                return tok[len(form):]
        if tok in ("C", "D"):
            return tok
        raise ParseError(f"expected an Action (C or D), got {tok!r}")

    def nat(self) -> str:
        """A Nat expression, kept as canonical space-joined source text."""
        tok = self.next()
        if tok == "(":
            depth, parts = 1, []
            while True:
                t = self.next()
                depth += (t == "(") - (t == ")")
                if depth == 0:
                    break
                parts.append(t)
            if not parts:
                raise ParseError("empty budget expression")
            for t in parts:
                self._check_nat_token(t)
            return " ".join(parts)
        self._check_nat_token(tok)
        return tok

    def _check_nat_token(self, t: str) -> None:
        if t.isdigit() or t in "()+*-/^" or t in self.params:
            return
        raise ParseError(f"budget expression uses {t!r}, which is not a Nat "
                         f"parameter of this definition")

    # -- programs
    def prog(self, under_bot: bool = False) -> Prog:
        tok = self.next()
        if tok == "(":
            p = self.prog(under_bot)
            self.expect(")")
            return p
        name = _ctor(tok, PROG_CTORS | UNSUPPORTED)
        if name in UNSUPPORTED:
            raise ParseError(f"constructor .{name} is outside the supported fragment")
        if name == "const":
            return Const(self.action())
        if name == "self":
            return Self()
        if name == "opp":
            return Opp()
        if name == "bot":
            return Bot(self.prog(under_bot=True))
        if name == "sim":
            return Sim(self.prog(), self.prog())
        if name == "ite":
            return Ite(self.prog(), self.action(), self.prog(), self.prog())
        if name == "search":
            return Search(self.nat(), self.formula(), self.prog(), self.prog())
        if _ctor(tok, FORMULA_CTORS):
            raise ParseError(f"formula constructor {tok!r} in program position")
        return self.reference(tok, under_bot)

    def reference(self, tok: str, under_bot: bool) -> Prog:
        if tok in self.lets:
            return self.lets[tok]
        bare = _bare_name(tok)
        if bare not in self.scope:
            raise ParseError(f"unknown name {tok!r} (not a constructor, a let, "
                             f"or a known bot)")
        d = self.scope[bare]
        args = [self.nat() for _ in d.params]
        body = rename_budgets(d.body, dict(zip(d.params, args)))
        if not under_bot and _has_placeholder(body):
            self.warnings.append(
                f"reference to {bare} is not wrapped in .bot: the enclosing frame's "
                f"subst will rewrite its .self/.opp (spec §3)")
        return body

    # -- formulas
    def formula(self) -> object:
        tok = self.next()
        if tok == "(":
            f = self.formula()
            self.expect(")")
            return f
        name = _ctor(tok, FORMULA_CTORS | UNSUPPORTED)
        if name in UNSUPPORTED:
            raise ParseError(f"constructor .{name} is outside the supported fragment")
        if name == "plays":
            return Plays(self.prog(), self.prog(), self.action())
        if name == "impl":
            return Impl(self.formula(), self.formula())
        if name == "neg":
            return Neg(self.formula())
        if name == "box":
            return Box(self.nat(), self.formula())
        if name == "eq":
            # the RHS is a frozen literal target: capture is impossible, no warning
            return Eq(self.prog(), self.prog(under_bot=True))
        raise ParseError(f"expected a Formula constructor, got {tok!r}")

    # -- definition body: lets, then the program
    def body(self) -> Prog:
        while self.peek() == "let":
            self.next()
            name = self.next()
            if not re.fullmatch(r"[A-Za-z_][\w']*", name):
                raise ParseError(f"bad let name {name!r}")
            if self.peek() == ":":
                self.next()
                self.expect("Prog")
            self.expect(":=")
            self.lets[name] = self.prog()
            if self.peek() == ";":
                self.next()
        return self.prog()


def _has_placeholder(p: Prog) -> bool:
    """Does ``p`` contain a ``.self``/``.opp`` that a ``subst`` would reach?"""
    if isinstance(p, (Self, Opp)):
        return True
    if isinstance(p, (Const, Bot)):
        return False
    if isinstance(p, Sim):
        return _has_placeholder(p.player) or _has_placeholder(p.opponent)
    if isinstance(p, Ite):
        return any(_has_placeholder(q) for q in (p.guard, p.then, p.els))
    if isinstance(p, Search):
        return True  # formulas almost always mention .self/.opp; be conservative
    return False


# ----------------------------------------------------------------- file parser


def parse_file(src: str, scope: dict[str, Definition] | None = None) -> ParsedFile:
    """Parse every ``def X … : Prog := …`` in ``src``, in order.

    ``scope`` holds the names visible to the file (the zoo); each parsed def is
    added to the scope of the defs after it, as Lean would.
    """
    scope = dict(scope or {})
    toks = tokenize(src)
    defs: dict[str, Definition] = {}
    order: list[str] = []
    warnings: list[str] = []
    i = 0
    while i < len(toks):
        if toks[i] != "def":
            i += 1
            continue
        name = _bare_name(toks[i + 1]) if i + 1 < len(toks) else ""
        j = i + 2
        params: list[str] = []
        while j < len(toks) and toks[j] == "(":
            k = toks.index(")", j)
            group = " ".join(toks[j:k + 1])
            inner = toks[j + 1:k]
            if ":" not in inner or inner[-1] != "Nat":
                raise ParseError(f"def {name}: only (x : Nat) parameters are "
                                 f"supported, got {group!r}")
            params += inner[:inner.index(":")]
            j = k + 1
        if toks[j:j + 3] != [":", "Prog", ":="]:
            raise ParseError(f"def {name}: expected ': Prog :=' after the parameters")
        parser = _Parser(toks[j + 3:], scope, tuple(params), warnings)
        body = parser.body()
        d = Definition(name, tuple(params), body)
        defs[name], scope[name] = d, d
        order.append(name)
        i = j + 3 + parser.i
    if not defs:
        raise ParseError("no `def … : Prog :=` found")
    return ParsedFile(defs, order, warnings)


# --------------------------------------------------------------- LLM extraction
_LEAN_BLOCK = re.compile(r"```(?:lean4?|Lean)?\s*\n(.*?)```", re.DOTALL)


def extract_lean(text: str) -> str | None:
    """The last fenced code block that contains a ``def`` (the final answer)."""
    blocks = [b for b in _LEAN_BLOCK.findall(text) if re.search(r"\bdef\b", b)]
    return blocks[-1] if blocks else None


@dataclass
class Sample:
    """One LLM reply, judged."""

    index: int
    raw: str
    source: str | None = None
    name: str | None = None
    params: tuple[str, ...] = ()
    program: Prog | None = None
    errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)

    @property
    def valid(self) -> bool:
        return self.program is not None and not self.errors


def judge(index: int, raw: str, zoo_scope: dict[str, Definition],
          main_name: str = "MyBot") -> Sample:
    """Extract, parse and lint one reply. Never raises: errors go on the sample."""
    s = Sample(index=index, raw=raw)
    s.source = extract_lean(raw)
    if s.source is None:
        s.errors.append("no ```lean code block containing a def")
        return s
    try:
        parsed = parse_file(s.source, zoo_scope)
    except (ParseError, IndexError, ValueError) as exc:
        s.errors.append(f"parse error: {exc}")
        return s
    s.warnings += parsed.warnings
    if main_name in parsed.defs:
        s.name = main_name
    else:
        s.name = parsed.order[-1]
        s.warnings.append(f"no def named {main_name}; using the last def, {s.name}")
    d = parsed.defs[s.name]
    s.params, s.program = d.params, d.body
    s.errors += lint(d)
    return s


def lint(d: Definition) -> list[str]:
    """Spec §11 rules that make a sample INVALID (not merely suspicious)."""
    from .prog import budgets

    errors = []
    for b in sorted(budgets(d.body)):
        if not any(t in d.params for t in b.split(" ")):
            errors.append(f"hard-coded budget {b!r}: budgets must be parameters "
                          f"(spec §6.2)")
    if has_search(d.body) and not d.params:
        errors.append("uses .search but takes no budget parameter")
    return errors
