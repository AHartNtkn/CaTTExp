"""
Machine checks for RC(3) on the lax square S
(notes/conjectures/answered/naturality-arbitrary-depth-r2-2026-11-18.md).

Level 1. The active-column factorisation (13): for a term T = coh_{P,A}[g] of
S whose strict image involves F, exactly one 0-column of P has distinct
substituted endpoints (x- and y+); the others are point-supported.  We build
R = the retained column as a one-column pasting context, d : P -> R and
e : R -> S with g = d[e] syntactically, and H = coh_{P,A}[d] over R.
Stability: for u over a vertical chain and s : C_n -> S, the H of u[s]
is literally the H of u.

Level 2. End-to-end 4-terms between parallel 3-terms of S that exchange a
path-only 3-cell (which splits f-|y^ inside a chain context) with a column
coherence in which F is a whole 2-disc: the naturality step (4) of the
response, plus a whiskered path 4-cell (Proposition P-infinity).

Everything is re-checked by catt.infer here and by the certified Agda
checker in src/CaTTExp/Generated/LaxSquareRC3.agda.
"""
import random
from catt import *
from rc2 import struct_cell, ident

# ---------------------------------------------------------------- the lax square
XM, XP, YM, YP, XU, YU, FM, FP, FF = range(9)
_S7 = (STAR, STAR, STAR, STAR,
       arr(STAR, v(XM), v(XP)), arr(STAR, v(YM), v(YP)),
       arr(STAR, v(XM), v(YM)), arr(STAR, v(XP), v(YP)))
P_ = comp2(_S7, 0, v(FM), v(YU))
Q_ = comp2(_S7, 0, v(XU), v(FP))
S = _S7 + (arr(arr(STAR, v(XM), v(YP)), P_, Q_),)
check_ctx(S)

# ---------------------------------------------------------------- columns of a pasting context
def column_ranges(tree):
    """[(start_vertex, end_vertex, first_var, end_var)] per 0-column."""
    def count(node):
        return sum(2 + count(c) for c in node)
    out, idx, prev = [], 1, 0
    for child in tree:
        y, f = idx, idx + 1
        end = f + 1 + count(child)
        out.append((prev, y, f, end))
        prev, idx = y, end
    return out

def support(t):
    return fv_tm(t)

def factor(G, T, x_end, y_end):
    """Active-column factorisation of T = coh_{P,A}[g] in G, where the active
    column must run x_end -> y_end and all other columns sit at a point.
    Returns (R, d, e, H)."""
    _, P, A, g = T
    tree = tree_of(P)
    cols = column_ranges(tree)
    active = [j for j, (s0, s1, _, _) in enumerate(cols) if g[s0] != g[s1]]
    assert len(active) == 1, 'not exactly one active column'
    j0 = active[0]
    s0, s1, f0, fend = cols[j0]
    assert g[s0] == v(x_end) and g[s1] == v(y_end), 'active column endpoints'
    R = tree_ctx((tree[j0],))
    pt = {x_end: v(0), y_end: v(1)}
    d = [None] * len(P)
    for j, (a, b, f, e_) in enumerate(cols):
        side = v(0) if j < j0 else v(1)
        if j != j0:
            for i in range(f, e_):
                sup = support(g[i])
                assert len(sup) == 1 and next(iter(sup)) == (x_end if j < j0 else y_end), \
                    'side column not point-supported'
                d[i] = rename_pt(g[i], pt)
    # 0-vertices
    d[0] = v(0)
    for j, (a, b, f, e_) in enumerate(cols):
        d[b] = v(0) if j < j0 else v(1)
    for k, i in enumerate(range(f0, fend)):
        d[i] = v(2 + k)
    d = tuple(d)
    e = (v(x_end), v(y_end)) + tuple(g[i] for i in range(f0, fend))
    H = ('coh', P, A, d)
    assert tuple(subst_tm(u, e) for u in d) == g, 'g != d[e]'
    assert subst_tm(H, e) == T
    infer(R, H)                       # H is well typed over R
    return R, d, e, H

def rename_pt(t, ren):
    if t[0] == 'v':
        return ren[t[1]]
    return ('coh', t[1], t[2], tuple(rename_pt(u, ren) for u in t[3]))

# ---------------------------------------------------------------- terms of S
def idv(x):
    return ident(S, x)

def paths_p():
    """Some 1-terms with path f- y^ (from x- to y+)."""
    f, y = v(FM), v(YU)
    ix, iy = idv(XM), idv(YP)
    out = [P_,
           comp2(S, 0, P_, iy),
           comp2(S, 0, ix, P_),
           comp2(S, 0, v(FM), comp2(S, 0, v(YU), iy)),
           comp2(S, 0, comp2(S, 0, ix, v(FM)), v(YU))]
    return out

def paths_q():
    out = [Q_,
           comp2(S, 0, Q_, idv(YP)),
           comp2(S, 0, idv(XM), Q_),
           comp2(S, 0, comp2(S, 0, idv(XM), v(XU)), v(FP))]
    return out

def kap(a, b):
    return struct_cell(S, a, b)

def random_F_term(rng):
    """A random 2-term of S with strict image F."""
    ps, qs = paths_p(), paths_q()
    a0, b1 = rng.choice(ps), rng.choice(qs)
    letters = []
    cur = a0
    for _ in range(rng.randint(0, 2)):
        nxt = rng.choice(ps)
        letters.append(kap(cur, nxt)); cur = nxt
    letters.append(kap(cur, P_)) if cur != P_ else None
    letters.append(v(FF))
    if rng.random() < 0.7:
        letters.append(kap(Q_, b1))
    # random bracketing of the vertical word
    def build(ls):
        if len(ls) == 1: return ls[0]
        k = rng.randint(1, len(ls) - 1)
        return comp2(S, 1, build(ls[:k]), build(ls[k:]))
    T = build(letters)
    # random point whiskers
    for _ in range(rng.randint(0, 2)):
        if rng.random() < 0.5:
            T = comp2(S, 0, idv(XM), T)
        else:
            T = comp2(S, 0, T, idv(YP))
    return T

# ---------------------------------------------------------------- level 2: an exchange instance
def V10_tree():
    """Column: position 1 has a 3-disc M : z10 -> z11, position 2 a 2-disc A2."""
    return (((( ),), ()),)

def exchange_instance():
    """alpha = (b . F) ; c  and  beta = c' ; ((b' . F) . 1_q), both
    T -> (kappa . F) . 1_q, where T = l . F, l a non-canonical path 2-cell,
    b, b' : l -> kappa two different path 3-cells, and c, c' the right unitor
    of the vertical word (a column coherence with F as a whole 2-disc).
    Returns (alpha, beta, Fill : alpha -> beta)."""
    ps = paths_p()
    p2, p3 = ps[1], ps[2]                 # (f-*y^)*1,  1*(f-*y^)
    l = comp2(S, 1, kap(p2, p3), kap(p3, P_))     # p2 => P_ via p3
    kk = kap(p2, P_)                               # canonical
    b = kap(l, kk)                                 # path 3-cell, one coherence
    mid = comp2(S, 1, kap(p2, ps[3]), kap(ps[3], P_))
    b1 = kap(l, mid); b2 = kap(mid, kk)
    bp = comp2(S, 2, b1, b2)                       # a different path 3-cell
    idq = ident_2(Q_)
    # column coherence: right unitor  U -> U . 1_q  for a vertical word U
    def runit(U):
        D2 = tree_ctx(disc_tree(2))
        r = comp2(D2, 1, v(4), ident_2_over(D2, v(3)))
        s = sub_from(D2, S, {4: U})
        return ('coh', D2, arr(infer(D2, v(4)), v(4), r), s)
    T0 = comp2(S, 1, l, v(FF))
    T1 = comp2(S, 1, kk, v(FF))
    alpha = comp2(S, 2, comp2(S, 1, b, v(FF)), runit(T1))
    beta = comp2(S, 2, runit(T0), comp2(S, 1, comp2(S, 1, bp, v(FF)), idq))
    assert infer(S, alpha) == infer(S, beta), 'not parallel'
    # step 1: naturality (4) over V(1,0): alpha -> runit(T0) ; ((b . F) . 1_q)
    beta_b = comp2(S, 2, runit(T0), comp2(S, 1, comp2(S, 1, b, v(FF)), idq))
    V = tree_ctx(V10_tree())
    # V vars: 0 x, 1 y, 2 h0, 3 h1, 4 z10, 5 z11, 6 M, 7 h2, 8 A2
    def runitV(U):
        D2 = tree_ctx(disc_tree(2))
        r = comp2(D2, 1, v(4), ident_2_over(D2, v(3)))
        s = sub_from(D2, V, {4: U})
        return ('coh', D2, arr(infer(D2, v(4)), v(4), r), s)
    idqV = ident_2_over(V, v(7))
    aV = comp2(V, 2, comp2(V, 1, v(6), v(8)), runitV(comp2(V, 1, v(5), v(8))))
    bV = comp2(V, 2, runitV(comp2(V, 1, v(4), v(8))),
               comp2(V, 1, comp2(V, 1, v(6), v(8)), idqV))
    nat = ('coh', V, arr(infer(V, aV), aV, bV), None)
    sV = sub_from(V, S, {6: b, 8: v(FF)})
    step1 = ('coh', V, nat[2], sV)
    assert infer(S, step1) == arr(infer(S, alpha), alpha, beta_b)
    # step 2: the path 4-cell b -> b' (no F; pulls back to the chain of f- y^),
    # whiskered by F, by 1_q, and behind runit(T0)
    xi = struct_cell(S, b, bp)
    w = comp2(S, 2, runit(T0), comp2(S, 1, comp2(S, 1, xi, v(FF)), idq))
    assert infer(S, w)[2] == beta_b and infer(S, w)[3] == beta
    fill = comp2(S, 3, step1, w)
    assert infer(S, fill) == arr(infer(S, alpha), alpha, beta)
    return alpha, beta, fill

def ident_2_over(G, h):
    """identity 2-cell on the 1-term h of G"""
    D1 = tree_ctx(disc_tree(1))
    s = sub_from(D1, G, {2: h})
    return ('coh', D1, arr(arr(STAR, v(0), v(1)), v(2), v(2)), s)

def ident_2(h):
    return ident_2_over(S, h)

# ---------------------------------------------------------------- mixed law (11)
def omega_R():
    """The context R of (11) and Omega_R, with Z -> F, M, N -> path 3-cells."""
    tree = ((((),), (), ((),)),)
    R = tree_ctx(tree)
    # vars: 0 x,1 y,2 a,3 b,4 L0,5 L1,6 M,7 c,8 Z,9 d,10 R0,11 R1,12 N
    M, Z, N = v(6), v(8), v(12)
    L0, L1, R0, R1 = v(4), v(5), v(10), v(11)
    def w3(m, z, r):
        return comp2(R, 1, comp2(R, 1, m, z), r)
    rLR = comp2(R, 2, w3(M, Z, R0), w3(L1, Z, N))
    rRL = comp2(R, 2, w3(L0, Z, N), w3(M, Z, R1))
    Om = ('coh', R, arr(infer(R, rLR), rLR, rRL), tuple(v(i) for i in range(len(R))))
    infer(R, Om)
    ps, qs = paths_p(), paths_q()
    m = kap(kap(ps[1], P_), comp2(S, 1, kap(ps[1], ps[2]), kap(ps[2], P_)))
    n = kap(kap(Q_, qs[1]), comp2(S, 1, kap(Q_, qs[2]), kap(qs[2], qs[1])))
    s = sub_from(R, S, {6: m, 8: v(FF), 12: n})
    inst = ('coh', R, Om[2], s)
    infer(S, inst)
    return inst

# ---------------------------------------------------------------- run
def main(n=40, seed=1):
    rng = random.Random(seed)
    facts = []
    seen = set()
    while len(facts) < n:
        T = random_F_term(rng)
        if T[0] != 'coh' or T in seen: continue
        seen.add(T)
        facts.append((T,) + factor(S, T, XM, YP))
    # 3-dimensional arities: whiskered and composed 3-cells with F-boundary
    ps = paths_p()
    b = kap(comp2(S, 1, kap(ps[1], ps[2]), kap(ps[2], P_)), kap(ps[1], P_))
    T3s = [comp2(S, 1, b, v(FF)),
           comp2(S, 0, idv(XM), comp2(S, 1, b, v(FF))),
           comp2(S, 0, comp2(S, 1, b, v(FF)), idv(YP))]
    for T in T3s:
        facts.append((T,) + factor(S, T, XM, YP))
    # stability: u over C_n, then substituted
    Cn = tree_ctx(((( ), ( )),))       # x, y, h0, h1, A1, h2, A2
    us = [comp2(Cn, 0, ident(Cn, 0), comp2(Cn, 1, v(4), v(6))),
          comp2(Cn, 0, comp2(Cn, 1, v(4), v(6)), ident(Cn, 1))]
    stab = 0
    for u in us:
        Ru, du, eu, Hu = factor(Cn, u, 0, 1)
        sg = sub_from(Cn, S, {4: kap(ps[1], P_), 6: v(FF)})
        us_ = subst_tm(u, sg)
        R2, d2, e2, H2 = factor(S, us_, XM, YP)
        assert H2 == Hu and R2 == Ru, 'stability fails'
        stab += 1
    alpha, beta, fill = exchange_instance()
    om = omega_R()
    print('factorisations:', len(facts), ' stability:', stab, ' exchange fill: ok', ' Omega_R: ok')
    return facts, (alpha, beta, fill), om

if __name__ == '__main__':
    main()


def emit_module():
    from emit_agda import Emitter
    facts, (alpha, beta, fill), om = main()
    E = Emitter()
    for i, (T, R, d, e, H) in enumerate(facts):
        E.check_typed('T%d' % i, S, T)        # T is a term of S
        E.check_typed('H%d' % i, R, H)        # H = coh_{P,A}[d] is a term of R
        E.check_eq('fact%d' % i, H, e, T)     # H[e] = T, syntactically
    A = infer(S, alpha)
    E.check_type('fill', S, fill, arr(A, alpha, beta))
    import rc3_pair
    for i, (T, R, d, e, H) in enumerate(rc3_pair.main()):
        E.check_typed('PT%d' % i, rc3_pair.C, T)
        E.check_typed('PH%d' % i, R, H)
        E.check_eq('pfact%d' % i, H, e, T)
    E.check_typed('omegaR', S, om)
    src = E.module('CaTTExp.Generated.LaxSquareRC3',
                   'RC(3) for the lax square: active-column factorisations (13), an exchange 4-term, and the mixed law (11); generalised factorisations for the cylinder of a composable pair. Built by tools/rc3_square.py and tools/rc3_pair.py.')
    open('../src/CaTTExp/Generated/LaxSquareRC3.agda', 'w').write(src)
    print('emitted', len(E.defs), 'definitions')
