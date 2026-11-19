"""The support-free presentation P through directed reachability in degree five.

Sources: original construction, formulas (4)–(29), and round 5, Response 3
(binary join). The sorts are the cell dimensions 0–4. Equations act in
both directions, rules from left to right. Input globes belong to the
individual diagram. Terms are variable names or (operation, *arguments).
The operation arguments are named x0, x1 in guards and boundary terms.
The s/t selectors are total and have their globularity laws in EQUATIONS.
At a unit input each directed schema has equal endpoints by the equations,
so its prescribed identity 5-cell is represented by reflexive reachability.
"""

from dataclasses import dataclass
from typing import Optional, Union

Term = Union[str, tuple]


@dataclass(frozen=True)
class Operation:
    inputs: tuple[int, ...]
    output: int
    guards: tuple[tuple[Term, Term], ...]
    source: Optional[Term] = None
    target: Optional[Term] = None


@dataclass(frozen=True)
class Schema:
    name: str
    variables: tuple[tuple[str, int], ...]
    guards: tuple[tuple[Term, Term], ...]
    left: Term
    right: Term


@dataclass(frozen=True)
class Cell:
    d: int
    term: Term

    def face(self, d, target=False):
        x = self
        while x.d > d:
            x = Cell(x.d - 1, (("t" if target else "s") + str(x.d), x.term))
        assert x.d == d
        return x

    @property
    def s(self):
        return self.face(self.d - 1)

    @property
    def t(self):
        return self.face(self.d - 1, True)

    @property
    def unit(self):
        return Cell(self.d + 1, (f"id{self.d}", self.term))


def paste(x, y):
    """Top composition or a single primitive whisker; arguments in order."""
    if x.d == y.d:
        op = f"comp{x.d}"
    elif x.d < y.d:
        op = f"left{x.d}_{y.d}"
    else:
        op = f"right{y.d}_{x.d}"
    return Cell(max(x.d, y.d), (op, x.term, y.term))


def comparison(name, x, y):
    return Cell(3 if name == "chi" else 4, (name, x.term, y.term))


def iota(x, y):
    return comparison("iota", x, y)


def adjacent(x, y, d):
    return (x.face(d, True).term, y.face(d).term)


def ctx(prefix, focus, suffix):
    if prefix is not None:
        focus = paste(prefix, focus)
    if suffix is not None:
        focus = paste(focus, suffix)
    return focus


# In the source paper "ab", "Ba", etc. suppress the stationary 1-whiskers
# needed to form ONE chronological 2-word from events on outer spans. Keep
# those whiskers explicit in every emitted term. The coordinate interval and
# its initial/final 1-cells are only notation used while building schemas.
@dataclass(frozen=True)
class Block:
    cell: Cell
    start: int
    initial: tuple[Cell, ...]
    final: tuple[Cell, ...]

    @property
    def stop(self):
        return self.start + len(self.initial)

    @classmethod
    def var(cls, cell, start):
        return cls(cell, start, (cell.face(1),), (cell.face(1, True),))

    def face(self, target=False):
        return Block(self.cell.t if target else self.cell.s, self.start,
                     self.initial, self.final)


def _extend(x, y, faces):
    cell = x.cell
    for i in reversed(range(y.start, x.start)):
        cell = paste(faces[i - y.start], cell)
    for i in range(x.stop, y.stop):
        cell = paste(cell, faces[i - y.start])
    return cell


def _merge(x, y, combine):
    """Chronological adjacency at the 1-boundary, with stationary spans."""
    assert x.stop >= y.start and y.stop >= x.start
    lo, hi = min(x.start, y.start), max(x.stop, y.stop)
    first = _extend(x, y, y.initial)
    second = _extend(y, x, x.final)
    initial = tuple(x.initial[i - x.start] if x.start <= i < x.stop else
                    y.initial[i - y.start] for i in range(lo, hi))
    final = tuple(y.final[i - y.start] if y.start <= i < y.stop else
                  x.final[i - x.start] for i in range(lo, hi))
    return Block(combine(first, second), lo, initial, final)


def word(x, y):
    return _merge(x, y, paste)


def inner(x, y):
    return _merge(x, y, iota)


def outer(op, x, y):
    assert x.stop == y.start
    return Block(comparison(op, x.cell, y.cell), x.start,
                 x.initial + y.initial, x.final + y.final)


def chi(x, y):
    return outer("chi", x, y)


def r(x, y):
    return outer("r", x, y)


def t(x, y):
    return outer("t", x, y)


def h(x, y):
    return outer("h", x, y)


def c(prefix, x, suffix):
    return ctx(prefix.cell if prefix else None, x.cell, suffix.cell if suffix else None)


def vertical(*cells):
    first, *rest = cells
    for b in rest:
        first = paste(first, b)
    return first


def binary_join(A, B):
    a, aa, b, bb = A.face(), A.face(True), B.face(), B.face(True)
    S = vertical(word(B, a).cell, chi(a, bb).cell, word(A, bb).cell)
    U0 = vertical(word(b, A).cell, word(B, aa).cell, chi(aa, bb).cell)
    plus = c(chi(a, b), inner(A, B), None)
    minus = c(None, inner(B, A), chi(aa, bb))
    t0 = c(None, t(a, B), word(A, bb))
    t1 = c(word(b, A), t(aa, B), None)
    r0 = c(None, r(A, b), word(aa, B))
    r1 = c(word(B, a), r(A, bb), None)
    return S, U0, plus, minus, t0, t1, r0, r1


OPERATIONS = {}
_equations = []
_rules = []


def _op(name, inputs, output, guards=(), bounds=None):
    s, t_ = (c.term for c in bounds) if bounds else (None, None)
    OPERATIONS[name] = Operation(inputs, output, tuple(guards), s, t_)


def _schema(name, variables, guards, lhs, rhs, directed=False):
    assert lhs.d == rhs.d
    if directed:
        assert lhs.d == 4
    (_rules if directed else _equations).append(Schema(
        name, tuple((v.term, v.d) for v in variables), tuple(guards),
        lhs.term, rhs.term))


def _sesquicategory():
    for n in range(1, 5):
        x, y, z = (Cell(n, v) for v in ("x0", "x1", "x2"))
        for letter in ("s", "t"):
            _op(f"{letter}{n}", (n,), n - 1)
        base = Cell(n - 1, "x0")
        _op(f"id{n-1}", (n - 1,), n, bounds=(base, base))
        _op(f"comp{n}", (n, n), n, (adjacent(x, y, n - 1),), (x.s, y.t))
        _schema(f"associativity {n}", [x, y, z],
                [adjacent(x, y, n - 1), adjacent(y, z, n - 1)],
                paste(paste(x, y), z), paste(x, paste(y, z)))
        _schema(f"left unit {n}", [x], [], paste(x.s.unit, x), x)
        _schema(f"right unit {n}", [x], [], paste(x, x.t.unit), x)
        if n >= 2:
            _schema(f"globular source {n}", [x], [], x.s.s, x.t.s)
            _schema(f"globular target {n}", [x], [], x.s.t, x.t.t)
        for k in range(1, n):
            # Each k-cell supplies a left/right action inside a (k-1)-hom.
            # Reversing the ordered list interchanges the directions throughout.
            for left in (True, False):
                name = "left" if left else "right"
                def act(low, high):
                    return paste(low, high) if left else paste(high, low)
                def glue(low, high):
                    return adjacent(low, high, k - 1) if left else adjacent(high, low, k - 1)
                u = Cell(k, "x0" if left else "x1")
                f = Cell(n, "x1" if left else "x0")
                src = act(u, f.s)
                tgt = act(u, f.t)
                _op(f"{name}{k}_{n}", (k, n) if left else (n, k), n,
                    (glue(u, f),), (src, tgt))
                l, ll, f, g = Cell(k, "l"), Cell(k, "m"), Cell(n, "f"), Cell(n, "g")
                F = Cell(n - 1, "F")
                body = act(l, F)
                _schema(f"{name} preserves identities {k},{n}", [l, F], [glue(l, F)],
                        act(l, F.unit), body.unit)
                _schema(f"{name} preserves composition {k},{n}", [l, f, g],
                        [glue(l, f), adjacent(f, g, n - 1)], act(l, paste(f, g)),
                        paste(act(l, f), act(l, g)))
                identity = f.face(k - 1, not left).unit
                _schema(f"{name} identity acts trivially {k},{n}", [f], [],
                        act(identity, f), f)
                pair = paste(l, ll) if left else paste(ll, l)
                _schema(f"{name} action {k},{n}", [l, ll, f],
                        [glue(l, ll), glue(ll, f)], act(pair, f), act(l, act(ll, f)))
                for j in range(k + 1, n):
                    m = Cell(j, "m")
                    for inside_left in (False, True):
                        a, b = (m, f) if inside_left else (f, m)
                        _schema(f"{name} preserves {'left' if inside_left else 'right'} {k},{j},{n}",
                                [l, m, f], [glue(l, f), adjacent(a, b, j - 1)],
                                act(l, paste(a, b)), paste(act(l, a), act(l, b)))
            l, f, rr = Cell(k, "l"), Cell(n, "f"), Cell(k, "r")
            _schema(f"commuting left and right actions {k},{n}", [l, f, rr],
                    [adjacent(l, f, k - 1), adjacent(f, rr, k - 1)],
                    paste(paste(l, f), rr), paste(l, paste(f, rr)))


def _comparisons():
    for op, p, q, cut in (("chi", 2, 2, 0), ("r", 3, 2, 0), ("t", 2, 3, 0),
                          ("iota", 3, 3, 1), ("h", 3, 3, 0)):
        x, y = Cell(p, "x0"), Cell(q, "x1")
        g = [adjacent(x, y, cut)]
        X, Y = Block.var(x, 0), Block.var(y, 1)
        if op == "chi":
            bounds = (word(Y, X).cell, word(X, Y).cell)
        elif op == "r":
            bounds = (vertical(chi(X.face(), Y).cell, word(X, Y).cell),
                      vertical(word(Y, X).cell, chi(X.face(True), Y).cell))
        elif op == "t":
            bounds = (vertical(word(Y, X).cell, chi(X, Y.face(True)).cell),
                      vertical(chi(X, Y.face()).cell, word(X, Y).cell))
        elif op == "iota":
            bounds = (vertical(paste(x.s, y), paste(x, y.t)),
                      vertical(paste(x, y.s), paste(x.t, y)))
        else:
            bounds = binary_join(X, Y)[:2]
        _op(op, (p, q), bounds[0].d + 1, g, bounds)
        for left in (True, False):
            u, v = (Cell(p - 1, "u"), y) if left else (x, Cell(q - 1, "v"))
            a, b = (u.unit, v) if left else (u, v.unit)
            whole = comparison(op, a, b)
            degenerate = comparison("r", u, v) if op == "h" and not left else whole.s.unit
            _schema(f"{op} {'left' if left else 'right'} degeneracy", [u, v],
                    [adjacent(u, v, cut)], whole, degenerate)

    for op, p, q in (("chi", 2, 2), ("r", 3, 2), ("t", 2, 3), ("iota", 3, 3)):
        l, x, y = Cell(2 if op == "iota" else 1, "l"), Cell(p, "x"), Cell(q, "y")
        k = l.d - 1
        def J(a, b):
            return comparison(op, a, b)
        _schema(f"{op} left whisker", [l, x, y], [adjacent(l, x, k), adjacent(x, y, k)],
                J(paste(l, x), y), paste(l, J(x, y)))
        _schema(f"{op} balanced whisker", [x, l, y], [adjacent(x, l, k), adjacent(l, y, k)],
                J(paste(x, l), y), J(x, paste(l, y)))
        _schema(f"{op} right whisker", [x, y, l], [adjacent(x, y, k), adjacent(y, l, k)],
                J(x, paste(y, l)), paste(J(x, y), l))
        if op == "iota":
            f = Cell(1, "f")
            _schema("iota preserves left 1-whiskering", [f, x, y],
                    [adjacent(f, x, 0), adjacent(x, y, 1)],
                    J(paste(f, x), paste(f, y)), paste(f, J(x, y)))
            _schema("iota preserves right 1-whiskering", [x, y, f],
                    [adjacent(x, y, 1), adjacent(y, f, 0)],
                    J(paste(x, f), paste(y, f)), paste(J(x, y), f))


def _outer_equations():
    A, A2, B, B2 = [Block.var(Cell(3, n), i) for n, i in (("A", 0), ("A2", 0), ("B", 1), ("B2", 1))]
    a, aa = A.face(), A.face(True)
    b, bb = B.face(), B.face(True)
    a1, a2, b1, b2 = [Block.var(Cell(2, n), i) for n, i in (("a1", 0), ("a2", 0), ("b1", 1), ("b2", 1))]
    av, bv = Block.var(Cell(2, "a"), 0), Block.var(Cell(2, "b"), 1)

    def eq(name, variables, joins, left, right):
        _schema(name, [v.cell for v in variables],
                [adjacent(u.cell, v.cell, d) for u, v, d in joins], left, right)

    eq("7a", [a1, a2, bv], [(a1, a2, 1), (a1, bv, 0)], chi(word(a1, a2), bv).cell,
       vertical(word(chi(a1, bv), a2).cell, word(a1, chi(a2, bv)).cell))
    eq("7b", [av, b1, b2], [(b1, b2, 1), (av, b1, 0)], chi(av, word(b1, b2)).cell,
       vertical(word(b1, chi(av, b2)).cell, word(chi(av, b1), b2).cell))

    def chain(u, v):
        return Block(paste(u.cell, v.cell), u.start, u.initial, u.final)
    eq("10", [A, A2, bv], [(A, A2, 2), (A, bv, 0)], r(chain(A, A2), bv).cell,
       vertical(c(None, r(A, bv), word(A2, bv)), c(word(bv, A), r(A2, bv), None)))
    eq("11", [av, B, B2], [(B, B2, 2), (av, B, 0)], t(av, chain(B, B2)).cell,
       vertical(c(word(B, av), t(av, B2), None), c(None, t(av, B), word(av, B2))))
    eq("12", [A, b1, b2], [(A, b1, 0), (b1, b2, 1)], r(A, word(b1, b2)).cell,
       vertical(c(word(b1, chi(a, b2)), word(r(A, b1), b2), None),
                c(None, word(b1, r(A, b2)), word(chi(aa, b1), b2))))
    eq("13", [a1, a2, B], [(a1, a2, 1), (a1, B, 0)], t(word(a1, a2), B).cell,
       vertical(c(None, word(t(a1, B), a2), word(a1, chi(a2, bb))),
                c(word(chi(a1, b), a2), word(a1, t(a2, B)), None)))
    eq("14", [A, a2, bv], [(A, a2, 1), (A, bv, 0)], r(word(A, a2), bv).cell,
       vertical(c(word(chi(a, bv), a2), inner(A, chi(a2, bv)), None),
                c(None, word(r(A, bv), a2), word(aa, chi(a2, bv)))))
    eq("15", [a1, A, bv], [(a1, A, 1), (A, bv, 0)],
       vertical(r(word(a1, A), bv).cell, c(None, inner(chi(a1, bv), A), word(a1, chi(aa, bv)))),
       c(word(chi(a1, bv), a), word(a1, r(A, bv)), None))
    eq("16", [av, B, b2], [(av, B, 0), (B, b2, 1)],
       vertical(c(None, inner(B, chi(av, b2)), word(chi(av, bb), b2)), t(av, word(B, b2)).cell),
       c(word(b, chi(av, b2)), word(t(av, B), b2), None))
    eq("17", [av, b1, B], [(av, b1, 0), (b1, B, 1)], t(av, word(b1, B)).cell,
       vertical(c(None, word(b1, t(av, B)), word(chi(av, b1), bb)),
                c(word(b1, chi(av, b)), inner(chi(av, b1), B), None)))
    d = Block.var(Cell(2, "d"), 2)
    eq("18", [av, bv, d], [(av, bv, 0), (bv, d, 0)], r(chi(av, bv), d).cell,
       t(av, chi(bv, d)).cell)

    F, F2 = Cell(3, "F"), Cell(3, "F2")
    cross = chi(av, bv).cell
    cross_guard = adjacent(av.cell, bv.cell, 0)
    _schema("20", [F, F2, av.cell, bv.cell],
            [cross_guard, adjacent(F, F2, 2), adjacent(F, cross, 1)],
            iota(paste(F, F2), cross),
            vertical(ctx(None, iota(F, cross), paste(F2, cross.t)),
                     ctx(paste(F, cross.s), iota(F2, cross), None)))
    _schema("21", [av.cell, bv.cell, F, F2],
            [cross_guard, adjacent(F, F2, 2), adjacent(cross, F, 1)],
            iota(cross, paste(F, F2)),
            vertical(ctx(paste(cross.s, F), iota(cross, F2), None),
                     ctx(None, iota(cross, F), paste(cross.t, F2))))

    _, _, plus, minus, t0, t1, r0, r1 = binary_join(A, B)
    join = h(A, B).cell
    eq("binary join factorization", [A, B], [(A, B, 0)], r1, vertical(join, minus))
    _schema("W", [A.cell, B.cell], [adjacent(A.cell, B.cell, 0)],
            vertical(t0, plus, r0), vertical(join, t1), True)


def _directed():
    def rule(name, x, y, k, left, right):
        _schema(name, [x, y], [adjacent(x, y, k)], left, right, True)
    X, Y = Cell(4, "X"), Cell(4, "Y")
    F, G = Cell(3, "F"), Cell(3, "G")
    rule("delta", X, Y, 2,
         vertical(paste(X.s, Y), paste(X, Y.t)), vertical(paste(X, Y.s), paste(X.t, Y)))
    u, uu = X.s.s, X.s.t
    v, vv = G.s, G.t
    rule("N_L", X, G, 1,
         vertical(iota(X.s, G), ctx(None, paste(X, v), paste(uu, G))),
         vertical(ctx(paste(u, G), paste(X, vv), None), iota(X.t, G)))
    u, uu = F.s, F.t
    v, vv = Y.s.s, Y.s.t
    rule("N_R", F, Y, 1,
         vertical(ctx(None, paste(u, Y), paste(F, vv)), iota(F, Y.t)),
         vertical(iota(F, Y.s), ctx(paste(F, v), paste(uu, Y), None)))

    L, B = Block.var(X, 0), Block.var(Cell(2, "b"), 1)
    A, A2 = L.face(), L.face(True)
    rule("U_r", X, B.cell, 0,
         vertical(r(A, B).cell, c(None, word(B, L), chi(A.face(True), B))),
         vertical(c(chi(A.face(), B), word(L, B), None), r(A2, B).cell))
    a, Q = Block.var(Cell(2, "a"), 0), Block.var(Y, 1)
    B, B2 = Q.face(), Q.face(True)
    rule("U_t", a.cell, Y, 0,
         vertical(c(None, word(Q, a), chi(a, B.face(True))), t(a, B2).cell),
         vertical(t(a, B).cell, c(chi(a, B.face()), word(a, Q), None)))


_sesquicategory()
_comparisons()
_outer_equations()
_directed()
EQUATIONS = tuple(_equations)
RULES = tuple(_rules)
