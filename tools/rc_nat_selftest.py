"""Self-test for tools/rc_nat.py (naturality lifts and oplax squares).
Run from tools/: python3 rc_nat_selftest.py. Every square is type-checked
by catt.infer inside rc_nat."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from catt import *
import rc_nat as N, rc_oracle as R

X = arr(STAR, v(0), v(1))

# 1. Lax square of a whisker f *0 g along e : f -> f'.
G1 = (STAR, STAR, X, X, arr(X, v(2), v(3)), STAR, arr(STAR, v(1), v(5)))
w, a, b = N.square(G1, {2}, {2: v(3)}, {2: v(4)}, comp2(G1, 0, v(2), v(6)), R.rc)
assert tdim_tm(G1, w) == 2

# 2. Lax square (depth 1) of the associator ((f g) h) -> (f (g h)) along e.
G2 = (STAR, STAR, X, X, arr(X, v(2), v(3)), STAR, arr(STAR, v(1), v(5)), STAR, arr(STAR, v(5), v(7)))
l = comp2(G2, 0, comp2(G2, 0, v(2), v(6)), v(8)); r = comp2(G2, 0, v(2), comp2(G2, 0, v(6), v(8)))
assoc = R.rc(G2, infer(G2, l), l, r)
w, a, b = N.square(G2, {2}, {2: v(3)}, {2: v(4)}, assoc, R.rc)
assert tdim_tm(G2, w) == 3

# 3. A 3-dimensional cap (an RC(2) answer) against a 3-cell event θ : α -> α',
#    lax and oplax.
G3 = (STAR, STAR, X, X, arr(X, v(2), v(3)), arr(X, v(2), v(3)), arr(arr(X, v(2), v(3)), v(4), v(5)),
      STAR, arr(STAR, v(1), v(7)), STAR, arr(STAR, v(7), v(9)))
c0 = lambda p, q: comp2(G3, 0, p, q); c1 = lambda p, q: comp2(G3, 1, p, q)
def asc(f):
    l = c0(c0(f, v(8)), v(10)); r = c0(f, c0(v(8), v(10))); return R.rc(G3, infer(G3, l), l, r)
s1 = c1(asc(v(2)), c0(v(4), c0(v(8), v(10))))
s2 = c1(c0(c0(v(4), v(8)), v(10)), asc(v(3)))
cap = R.rc(G3, infer(G3, s1), s1, s2)
w, a, b = N.square(G3, {4}, {4: v(5)}, {4: v(6)}, cap, R.rc)
assert tdim_tm(G3, w) == 4
w, a, b = N.nat_op(G3, {4}, {4: v(5)}, {4: v(6)}, cap, R.rc)
assert infer(G3, w) == arr(infer(G3, a), b, a)

# 4. A reassociation-and-unit coherence over a vertical chain of five 2-cells,
#    ((((id a) b) c) d) e => a (b ((c d) e)), with moving middle cells: the
#    filler is transferred from pasted elementary associator and unitor squares
#    (_assoc_filler), not searched for in the 31-variable cylinder.
G4 = [STAR, STAR, X]
for k in range(5):
    G4.append(X); G4.append(arr(X, v(len(G4) - 3 if k else 2), v(len(G4) - 1)))
G4 = tuple(G4)
a4, b4, c4, d4, e4 = (v(i) for i in maximal_vars(G4))
i4 = ('coh', (STAR, STAR, X), arr(X, v(2), v(2)), (v(0), v(1), v(2)))
k1 = lambda p, q: comp2(G4, 1, p, q)
l4 = k1(k1(k1(k1(k1(i4, a4), b4), c4), d4), e4)
r4 = k1(a4, k1(b4, k1(k1(c4, d4), e4)))
B4 = arr(infer(G4, l4), l4, r4)
for Y4 in ({6}, {5, 6, 8}, {6, 7, 8, 10}, {8, 9, 10, 12}):
    C4, mi4, pl4, up4 = N.cylinder(G4, Y4)
    c4h = ('coh', G4, B4, tuple(v(mi4[i]) for i in range(len(G4))))
    Yi4 = frozenset(mi4[q] for q in Y4)
    lf4 = lambda w: N.nat_in(C4, Yi4, {mi4[q]: v(pl4[q]) for q in Y4}, {mi4[q]: v(up4[q]) for q in Y4}, w, R.rc)
    a_, b_ = N.boundary_ab(C4, c4h, lambda w: bool(fv_tm(w) & Yi4), lf4, lambda w: N._swap(w, mi4, pl4, Y4))
    K4 = N._assoc_filler(G4, B4, frozenset(Y4), C4, mi4, pl4, up4, a_, b_, R.rc)
    assert K4 is not None and infer(C4, K4) == arr(infer(C4, a_), a_, b_)

print('rc_nat self-test: all squares built and type-checked')
