"""
The generalised active-column factorisation for the cylinder of a composable
pair, Q = (x, y, z, f, g), Y = Var(Q)  (relative-coherence.md §7.5).

Inactive columns now carry paths: they are pulled back to the chain of their
path (positionally; the 1-skeleton is acyclic), the active column is retained
as is.  We check, on generated 2-terms with generator-valued strict image:
  * exactly one active column (no two 2-generators are *0-composable here);
  * g = d[e] syntactically, and H = coh_{P,A}[d] is a term of the retained R;
  * stability: for u over R and the substitution e : R -> Gamma, the
    factorisation of u[e] is literally the factorisation of u.
"""
import random
from catt import *
from rc2 import struct_cell, ident, path, chain_ren
from rc3_square import column_ranges, rename_pt

# Q^Y for the composable pair
names = ['xm', 'xp', 'ym', 'yp', 'zm', 'zp']
G0 = [STAR] * 6
XM, XP, YM, YP, ZM, ZP = range(6)
def e(a, b): return arr(STAR, v(a), v(b))
G0 += [e(XM, XP), e(YM, YP), e(ZM, ZP), e(XM, YM), e(XP, YP), e(YM, ZM), e(YP, ZP)]
XU, YU, ZU, FM, FP, GM, GP = range(6, 13)
G1 = tuple(G0)
fU = arr(arr(STAR, v(XM), v(YP)), comp2(G1, 0, v(FM), v(YU)), comp2(G1, 0, v(XU), v(FP)))
G2 = G1 + (fU,)
gU = arr(arr(STAR, v(YM), v(ZP)), comp2(G2, 0, v(GM), v(ZU)), comp2(G2, 0, v(YU), v(GP)))
C = G2 + (gU,)
FU, GU = 13, 14
check_ctx(C)

def has_gen(t):
    return any(tdim(C[i]) >= 1 for i in fv_tm(t))   # uses a 2-variable

def factor_gen(G, T):
    """Generalised factorisation of T = coh_{P,A}[g] in G.  Returns (R, d, e, H)."""
    _, P, A, g = T
    tree = tree_of(P)
    cols = column_ranges(tree)
    two = lambda t: any(tdim(G[i]) >= 1 for i in fv_tm(t))
    active = [j for j, (s0, s1, f, end) in enumerate(cols)
              if any(two(g[i]) for i in range(f, end))]
    assert len(active) == 1, 'active columns: %s' % active
    j0 = active[0]
    Rtree, d, eta = [], [None] * len(P), [g[0]]
    d[0] = v(0)
    cur = 0            # current R vertex var
    nR = 1
    for j, (s0, s1, f, end) in enumerate(cols):
        if j == j0:
            Rtree.append(tree[j])
            # R vars for this column: y = nR, then f.. positional
            sub_n = end - f
            ycol = nR
            ren_pos = {}
            # in tree_ctx order: y, f, then the subtree vars
            d[s1] = v(ycol)
            eta.append(g[s1])
            for k, i in enumerate(range(f, end)):
                d[i] = v(ycol + 1 + k)
                eta.append(g[i])
            nR = ycol + 1 + sub_n
            cur = ycol
        else:
            w, a, b = path(G, g[f])
            assert v(a) == g[s0] and v(b) == g[s1]
            ren = {a: cur}
            for edge in w:
                y_, f_ = nR, nR + 1
                Rtree.append(())
                ren[edge] = f_; ren[G[edge][3][1]] = y_
                eta += [v(G[edge][3][1]), v(edge)]
                nR += 2
                cur = y_
            for i in range(f, end):
                assert not two(g[i])
                d[i] = rename(g[i], ren)
            d[s1] = v(cur)
    R = tree_ctx(tuple(Rtree))
    d, eta = tuple(d), tuple(eta)
    assert len(eta) == len(R)
    H = ('coh', P, A, d)
    assert tuple(subst_tm(u, eta) for u in d) == g, 'g != d[e]'
    infer(R, H)
    return R, d, eta, H

def rename(t, ren):
    if t[0] == 'v':
        return v(ren[t[1]])
    return ('coh', t[1], t[2], tuple(rename(u, ren) for u in t[3]))

def kap(a, b): return struct_cell(C, a, b)

def gen_terms(rng, n):
    """2-terms of C with a generator in the image, with path columns."""
    out = []
    fy = comp2(C, 0, v(FM), v(YU)); xf = comp2(C, 0, v(XU), v(FP))
    gz = comp2(C, 0, v(GM), v(ZU)); yg = comp2(C, 0, v(YU), v(GP))
    base = [v(FU), v(GU),
            comp2(C, 0, v(FM), v(GU)),                  # f- . g^   (path column f-)
            comp2(C, 0, v(FU), v(GP)),                  # f^ . g+   (path column g+)
            comp2(C, 1, comp2(C, 0, v(FM), v(GU)),      # (f- . g^) ; (f^ . g+)
                  kap(comp2(C, 0, v(FM), yg), comp2(C, 0, fy, v(GP))))]
    base.append(comp2(C, 1, base[-1], comp2(C, 0, v(FU), v(GP))))
    for t in base:
        out.append(t)
    while len(out) < n:
        t = rng.choice(base)
        r = rng.random()
        if r < 0.3:
            t = comp2(C, 0, ident(C, infer(C, t)[1][2][1]), t)
        elif r < 0.6:
            t = comp2(C, 0, t, ident(C, infer(C, t)[1][3][1]))
        else:
            src1 = infer(C, t)[2]
            w, a, b = path(C, src1)
            # precompose a path cell from another bracketing
            alt = comp2(C, 0, ident(C, a), src1)
            t = comp2(C, 1, kap(alt, src1), t)
        out.append(t)
    return out

def main(n=40, seed=3):
    rng = random.Random(seed)
    res = []
    seen = set()
    for T in gen_terms(rng, n):
        if T[0] != 'coh' or T in seen: continue
        seen.add(T)
        R, d, eta, H = factor_gen(C, T)
        # stability: factorise H over R, and H[eta] = T over C
        R2, d2, e2, H2 = factor_gen(R, H)
        assert R2 == R and H2 == H, 'stability (H over R)'
        res.append((T, R, d, eta, H))
    # stability for a composite over R: u = H ; (path cell over R), then u[eta]
    stab = 0
    for (T, R, d, eta, H) in res[:12]:
        tgt1 = infer(R, H)[3]
        w, a, b = path(R, tgt1)
        alt = comp2(R, 0, tgt1, ident(R, b))
        u = comp2(R, 1, H, struct_cell(R, tgt1, alt))
        Ru, du, eu, Hu = factor_gen(R, u)
        Rs, ds, es, Hs = factor_gen(C, subst_tm(u, eta))
        assert Ru == Rs and Hu == Hs, 'stability (u over R)'
        stab += 1
    print('pair cylinder: factorisations', len(res), ' stability', stab)
    return res

if __name__ == '__main__':
    main()
