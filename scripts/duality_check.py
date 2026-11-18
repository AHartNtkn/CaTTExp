"""Which dualities D_K commute with the Gray tensor of Steiner complexes,
under the canonical generator correspondence (notes/closed-structure.md, Part D).

Globe D^p: basis s_i, t_i (0<=i<p) and top c_p; boundary d(x_i) = t_{i-1} - s_{i-1}.
Tensor: d(x(*)y) = dx(*)y + (-1)^|x| x(*)dy.
Duality reversing the cells of dimensions in K: d^K(x) = eps(|x|) d(x),
eps(n) = -1 iff n in K   (a reversed n-cell swaps its (n-1)-source and target).
For every K (subset of 1..N) and p,q <= P it compares
  D_K(D^p (*) D^q)   with   D_K D^p (*) D_K D^q   (identity on generators)
  and with                  D_K D^q (*) D_K D^p   (swap x(*)y -> y(*)x),
then lists the K for which the comparison holds for all p,q.
"""
import itertools

def globe(p):
    gens = [('s', i) for i in range(p)] + [('t', i) for i in range(p)] + [('c', p)]
    dim = lambda g: g[1]
    def d(g):
        n = dim(g)
        if n == 0: return {}
        return {('t', n - 1) if n - 1 < p else None: 1, ('s', n - 1): -1}
    return gens, dim, d

def tensor(X, Y, epsX, epsY, epsT):
    gx, dx, bx = X; gy, dy, by = Y
    gens = [(a, b) for a in gx for b in gy]
    dim = lambda g: dx(g[0]) + dy(g[1])
    def d(g):
        a, b = g; out = {}
        for a2, c in bx(a).items():
            c *= epsX(dx(a))
            out[(a2, b)] = out.get((a2, b), 0) + c
        for b2, c in by(b).items():
            c *= epsY(dy(b)) * (-1) ** dx(a)
            out[(a, b2)] = out.get((a, b2), 0) + c
        e = epsT(dim(g))
        return {k: v * e for k, v in out.items() if v}
    return gens, dim, d

def check(K, P=3):
    eps = lambda n: -1 if n in K else 1
    one = lambda n: 1
    ok_id = ok_sw = True
    for p in range(P + 1):
        for q in range(P + 1):
            Dp, Dq = globe(p), globe(q)
            lhs = tensor(Dp, Dq, one, one, eps)          # D_K(D^p (*) D^q)
            rid = tensor(Dp, Dq, eps, eps, one)          # D_K D^p (*) D_K D^q
            rsw = tensor(Dq, Dp, eps, eps, one)          # D_K D^q (*) D_K D^p
            for g in lhs[0]:
                if lhs[2](g) != rid[2](g): ok_id = False
                sw = {(k[1], k[0]): v for k, v in lhs[2](g).items()}
                if sw != rsw[2]((g[1], g[0])): ok_sw = False
    return ok_id, ok_sw

N = 6
res = {}
for r in range(N + 1):
    for K in itertools.combinations(range(1, N + 1), r):
        res[K] = check(set(K))
print("K with D_K(X(*)Y) = D_K X (*) D_K Y :", [K for K, v in res.items() if v[0]])
print("K with D_K(X(*)Y) = D_K Y (*) D_K X :", [K for K, v in res.items() if v[1]])
