"""Independent re-check of the E6 round-7 response, section 5: count the cells of nu(K),
K = lambda D2 (x) lambda D2 (x) lambda D2, of dimension 2 and 3 whose 0- and 1-rows are those
of the top atom (claimed 54 and 874). Uses 0/1 coefficients (radicality for these strongly
loop-free complexes) and the cochain bound |x3| <= 7. Run: python3 scripts/e6/r7_tableaux.py (~3 min)."""
import itertools
from collections import defaultdict
# lambda D2: x0,x1 (dim0); f0,f1 (dim1); A (dim2)
D = {'x0':0,'x1':0,'f0':1,'f1':1,'A':2}
d1 = {'x0':{},'x1':{},'f0':{'x1':1,'x0':-1},'f1':{'x1':1,'x0':-1},'A':{'f1':1,'f0':-1}}
basis = list(itertools.product(D, D, D))
dim = {b: sum(D[c] for c in b) for b in basis}
def bd(b):
    out = defaultdict(int); sign = 1
    for i in range(3):
        for c, k in d1[b[i]].items():
            nb = b[:i] + (c,) + b[i+1:]; out[nb] += sign * k
        sign *= (-1) ** D[b[i]]
    return {k: v for k, v in out.items() if v}
def bdc(ch):
    out = defaultdict(int)
    for b, k in ch.items():
        for c, v in bd(b).items(): out[c] += k * v
    return {k: v for k, v in out.items() if v}
def pos(ch): return {k: v for k, v in ch.items() if v > 0}
def neg(ch): return {k: -v for k, v in ch.items() if v < 0}
top = ('A', 'A', 'A')
atom = {6: ({top: 1}, {top: 1})}
for k in range(5, -1, -1):
    m, p = atom[k + 1]
    atom[k] = (neg(bdc(m)), pos(bdc(p)))
target = {}
for b, v in atom[1][1].items(): target[b] = target.get(b, 0) + v
for b, v in atom[1][0].items(): target[b] = target.get(b, 0) - v
target = {k: v for k, v in target.items() if v}
B2 = [b for b in basis if dim[b] == 2]; B3 = [b for b in basis if dim[b] == 3]
def solve(vars_, rhs):
    """all 0/1 vectors x on vars_ with bdc(x) == rhs"""
    rows = defaultdict(dict)
    for i, b in enumerate(vars_):
        for c, v in bd(b).items(): rows[c][i] = v
    keys = set(rows) | set(rhs)
    last = {c: max(rows[c]) if rows[c] else -1 for c in keys}
    by_last = defaultdict(list)
    for c in keys: by_last[last[c]].append(c)
    res = []; x = [0] * len(vars_)
    def chk(i):
        for c in by_last[i]:
            if sum(v * x[j] for j, v in rows[c].items()) != rhs.get(c, 0): return False
        return True
    if not chk(-1): return res
    def go(i):
        if i == len(vars_): res.append(tuple(x)); return
        for val in (0, 1):
            x[i] = val
            if chk(i): go(i + 1)
        x[i] = 0
    go(0); return res
cells2 = solve(B2, target)
print('2-cells with the top atom 1-boundary:', len(cells2))
vec = [frozenset(B2[i] for i, v in enumerate(c) if v) for c in cells2]
# differences w - u, with multiplicity
from fractions import Fraction
diff = defaultdict(int)
for u in vec:
    for w in vec:
        d = {k: (1 if k in w else 0) - (1 if k in u else 0) for k in u | w}
        diff[frozenset((k, v) for k, v in d.items() if v)] += 1
# a rational cochain f on K2 with f(bd b) = 1 for every b in B3 bounds the size of x3:
# |x3| = f(bd x3) = f(w - u).  Solve by Gaussian elimination over Q.
idx = {b: i for i, b in enumerate(B2)}
rows = []
for b in B3:
    r = [Fraction(0)] * (len(B2) + 1)
    for c, v in bd(b).items(): r[idx[c]] += v
    r[-1] = Fraction(1); rows.append(r)
n = len(B2); piv = []; R = rows; rk = 0
for col in range(n):
    pr = next((i for i in range(rk, len(R)) if R[i][col] != 0), None)
    if pr is None: continue
    R[rk], R[pr] = R[pr], R[rk]
    inv = 1 / R[rk][col]; R[rk] = [x * inv for x in R[rk]]
    for i in range(len(R)):
        if i != rk and R[i][col] != 0:
            fac = R[i][col]; R[i] = [a - fac * b for a, b in zip(R[i], R[rk])]
    piv.append(col); rk += 1
assert all(any(x != 0 for x in r[:-1]) or r[-1] == 0 for r in R), 'no cochain f'
f = [Fraction(0)] * n
for i, col in enumerate(piv): f[col] = R[i][-1]
for b in B3: assert sum(f[idx[c]] * v for c, v in bd(b).items()) == 1
bound = max(sum(f[idx[k]] * v for k, v in d) for d in diff)
print('size bound for x3:', bound)
count3 = 0
for k in range(int(bound) + 1):
    for sub in itertools.combinations(B3, k):
        d = defaultdict(int)
        for b in sub:
            for c, v in bd(b).items(): d[c] += v
        key = frozenset((c, v) for c, v in d.items() if v)
        count3 += diff.get(key, 0)
print('3-cells (tables x0..x3) with that 1-boundary, identities included:', count3)
