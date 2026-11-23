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

print('rc_nat self-test: all squares built and type-checked')
