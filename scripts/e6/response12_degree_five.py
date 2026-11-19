"""Additional directed 5-boundaries of Responses 8–12 in the free presentation.

These two-variable schemas record existence of a path. At units the shifted
join specializes to an identity or N_L. H_L specializes to an identity or
U_r, H_R to an identity, and K to W or an identity (left/right unit order).
J at a left unit is W with a preceding right variation, followed by H_R
with a trailing t_1. At a right unit it is K. Thus grounding the boundaries
also at units gives exactly the reachability of the prescribed unit paths.
"""

from reachability_theory import (
    Block, Cell, Schema, adjacent, binary_join, chi, h, iota, vertical, word,
)


def _rule(name, left, right, cut, source, target):
    assert source.d == target.d == 4
    return Schema(name, ((left.term, left.d), (right.term, right.d)),
                  (adjacent(left, right, cut),), source.term, target.term)


def _shifted_join(x, y):
    # Inside the hom, stationary whiskers are 2-cells and the crossing is iota.
    A = Block(x, 0, (x.face(2),), (x.face(2, True),))
    B = Block(y, 1, (y.face(2),), (y.face(2, True),))
    a, aa, b, bb = A.face(), A.face(True), B.face(), B.face(True)
    return _rule("shifted_join", x, y, 1,
                 vertical(word(B, a).cell, iota(a.cell, bb.cell), word(A, bb).cell),
                 vertical(word(b, A).cell, word(B, aa).cell, iota(aa.cell, bb.cell)))


def _variation(A, B):
    """Insert the one 4-dimensional input into the histories S, V0 and U0."""
    assert sorted((A.cell.d, B.cell.d)) == [3, 4]
    a, aa = (Block.var(A.cell.face(2, target), 0) for target in (False, True))
    b, bb = (Block.var(B.cell.face(2, target), 1) for target in (False, True))
    # Exactly one factor of each vertical product has degree four. The
    # preceding and following 3-events whisker that occurrence in place.
    S = vertical(word(B, a).cell, chi(a, bb).cell, word(A, bb).cell)
    V0 = vertical(chi(a, b).cell, word(a, B).cell, word(A, bb).cell)
    U0 = vertical(word(b, A).cell, word(B, aa).cell, chi(aa, bb).cell)
    return S, V0, U0


def _extra_rules():
    x, y = Cell(4, "X"), Cell(4, "Y")
    X, Y = Block.var(x, 0), Block.var(y, 1)
    A, B = Block.var(Cell(3, "A"), 0), Block.var(Cell(3, "B"), 1)
    A0, A1, B0, B1 = X.face(), X.face(True), Y.face(), Y.face(True)

    xS, xV0, xU0 = _variation(X, B)
    yS, _, yU0 = _variation(A, Y)
    hl = _rule("H_L", x, B.cell, 0,
               vertical(h(A0, B).cell, xU0), vertical(xS, h(A1, B).cell))
    hr = _rule("H_R", A.cell, y, 0,
               vertical(yS, h(A, B1).cell), vertical(h(A, B0).cell, yU0))

    # a,b,c,h,f denote t0, iota+, r0, h, t1 in the hexagon. A move
    # following x or y uses the target face of that variation.
    _, _, _, _, a, _, _, _ = binary_join(A0, B)
    _, _, b, _, _, f, c, _ = binary_join(A1, B)
    k = _rule("K", x, B.cell, 0, vertical(a, xV0, b, c),
              vertical(xS, h(A1, B).cell, f))

    yS, _, _ = _variation(A0, Y)
    _, xV0, _ = _variation(X, B1)
    xS, _, _ = _variation(X, B0)
    _, _, yU0 = _variation(A1, Y)
    _, _, _, _, a, _, _, _ = binary_join(A0, B1)
    _, _, b, _, _, f, c, _ = binary_join(A1, B1)
    j = _rule("J", x, y, 0, vertical(yS, a, xV0, b, c),
              vertical(xS, h(A1, B0).cell, yU0, f))
    return _shifted_join(x, y), hl, hr, k, j


EXTRA_RULES = _extra_rules()
