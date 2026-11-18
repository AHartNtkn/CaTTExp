"""
Checks toward RC(3) on the full cylinder of a finite chain
x0 -> x1 -> ... -> xk  (round-5 answer,
notes/conjectures/answered/naturality-arbitrary-depth-r5-2026-11-18.md, §§1-2),
for k = 3.

    x_i-, x_i+, v_i : x_i- -> x_i+            (i = 0..k)
    a_i-, a_i+, F_i : a_i- *0 v_i => v_{i-1} *0 a_i+   (i = 1..k)

We build and check:
  * the raw letters E_i^{a,b} = L_i- *0 (F_i *0 R_i+)            (2)
  * the normal forms N_w(A, B) for every forced word w on every pair of
    outer endpoints, including the boxed three-letter form (5)
  * the multiplication mu_{u,v} : N_u(A,B) . N_v(B,C) => N_uv(A,C)  (7)
    for every split of every word (a reassociation coherence on C_N, then the
    contraction m_p inserted as a composition coherence on V_N(0..1..0))
  * the fold 4-cells of §2.2: overlapping pairs (direct 4-coherence on the
    path) and disjoint pairs (interchange on V(1,1))
  * literal factorisation of generated 2-terms through a one-column frame
    P_l *0 C_n *0 P_r, with stability.
Everything is re-checked by catt.infer here and by the certified Agda
checker in src/CaTTExp/Generated/ChainCylinderRC3.agda.
"""
import random, itertools
from catt import *
from rc2 import struct_cell, ident, path, lfold
from rc3_wedge import factor_cols, eta_witness, two
from rc3_square import column_ranges

K = 3
# ---------------------------------------------------------------- the context
def build(k):
    G = []
    XM, XP, VV = {}, {}, {}
    for i in range(k + 1):
        XM[i] = len(G); G.append(STAR)
        XP[i] = len(G); G.append(STAR)
        VV[i] = len(G); G.append(arr(STAR, v(XM[i]), v(XP[i])))
    AM, AP, FF = {}, {}, {}
    for i in range(1, k + 1):
        AM[i] = len(G); G.append(arr(STAR, v(XM[i - 1]), v(XM[i])))
        AP[i] = len(G); G.append(arr(STAR, v(XP[i - 1]), v(XP[i])))
        Gt = tuple(G)
        s = comp2(Gt, 0, v(AM[i]), v(VV[i]))
        t = comp2(Gt, 0, v(VV[i - 1]), v(AP[i]))
        FF[i] = len(G); G.append(arr(arr(STAR, v(XM[i - 1]), v(XP[i])), s, t))
    G = tuple(G)
    check_ctx(G)
    return G, XM, XP, VV, AM, AP, FF

C, XM, XP, VV, AM, AP, FF = build(K)

def rnest(ts):
    t = ts[-1]
    for u in reversed(ts[:-1]):
        t = comp2(C, 0, u, t)
    return t

def lnest(ts):
    return lfold(C, 0, ts)

def kap(a, b): return struct_cell(C, a, b)

def letter(i, a, b):
    """E_i^{a,b} = L_i- *0 (F_i *0 R_i+), empty whiskers omitted."""
    L = [v(AM[j]) for j in range(a + 1, i)]
    R = [v(AP[j]) for j in range(i + 1, b + 1)]
    core = v(FF[i])
    if R:
        core = comp2(C, 0, core, rnest(R))
    if L:
        core = comp2(C, 0, rnest(L), core)
    return core

def P_edges(j, a, b):
    return ([v(AM[i]) for i in range(a + 1, j + 1)] + [v(VV[j])] +
            [v(AP[i]) for i in range(j + 1, b + 1)])

def S(i, a, b): return infer(C, letter(i, a, b))[2]
def T(i, a, b): return infer(C, letter(i, a, b))[3]

def N_list(w, A, B, a, b):
    """The list (3) for the forced word w = (r, r-1, ..., s+1); w empty: [kappa(A,B)]."""
    if not w:
        return [kap(A, B)]
    out = [kap(A, S(w[0], a, b))]
    for idx, i in enumerate(w):
        out.append(letter(i, a, b))
        nxt = S(w[idx + 1], a, b) if idx + 1 < len(w) else B
        out.append(kap(T(i, a, b), nxt))
    return out

def N(w, A, B, a, b):
    return lfold(C, 1, N_list(w, A, B, a, b))

# ---------------------------------------------------------------- C_N, V_N
def CN(n):
    return tree_ctx(((tuple(() for _ in range(n))),))
def zvar(i): return v(2 + 2 * i)          # i-th 2-variable of C_N (1-based)

def mu(u, v_, A, B, Cc, a, b):
    Lu, Lv = N_list(u, A, B, a, b), N_list(v_, B, Cc, a, b)
    L = Lu + Lv
    n, m = len(L), len(Lu)
    P = CN(n)
    zs = [zvar(i) for i in range(1, n + 1)]
    src = comp2(P, 1, lfold(P, 1, zs[:m]), lfold(P, 1, zs[m:]))
    pair = comp2(P, 1, zs[m - 1], zs[m])
    mid = lfold(P, 1, zs[:m - 1] + [pair] + zs[m + 1:])
    A3 = infer(P, src)
    sig = sub_from(P, C, {2 + 2 * i: L[i - 1] for i in range(1, n + 1)})
    step1 = subst_tm(('coh', P, arr(A3, src, mid), tuple(v(i) for i in range(len(P)))), sig)
    # V: column of n-1 slots, slot m (1-based) carries a 3-cell
    slots = [() for _ in range(n - 1)]
    slots[m - 1] = ((),)
    V = tree_ctx((tuple(slots),))
    # variables of V: the 2-variables in column order; the slot-m one has a
    # 3-cell child h : z^0 => z^1
    twos = [i for i, A in enumerate(V) if tdim(A) == 1]
    threes = [i for i, A in enumerate(V) if tdim(A) == 2]
    h = threes[0]
    z0, z1 = V[h][2], V[h][3]
    others = [v(i) for i in twos if v(i) not in (z0, z1)]
    left, right = others[:m - 1], others[m - 1:]
    vs = lfold(V, 1, left + [z0] + right)
    vt = lfold(V, 1, left + [z1] + right)
    B3 = infer(V, vs)
    pterm = comp2(C, 1, L[m - 1], L[m])
    # contraction m_p : kappa(X,Y) . kappa(Y,Z) => kappa(X,Z)
    X_ = infer(C, L[m - 1])[2]; Z_ = infer(C, L[m])[3]
    kxz = kap(X_, Z_)
    mp = struct_cell(C, pterm, kxz)
    imgs = {h: mp}
    for var, t in zip([i for i in twos if v(i) not in (z0, z1)], L[:m - 1] + L[m + 1:]):
        imgs[var] = t
    sigV = sub_from(V, C, imgs)
    step2 = subst_tm(('coh', V, arr(B3, vs, vt), tuple(v(i) for i in range(len(V)))), sigV)
    res = comp2(C, 2, step1, step2)
    lhs = comp2(C, 1, N(u, A, B, a, b), N(v_, B, Cc, a, b))
    want = arr(infer(C, lhs), lhs, N(u + v_, A, Cc, a, b))
    assert infer(C, res) == want, 'mu has the wrong type'
    return res, want

def brackets(ts):
    """All bracketings of a list of composable 1-terms."""
    if len(ts) == 1:
        yield ts[0]; return
    for i in range(1, len(ts)):
        for l in brackets(ts[:i]):
            for r in brackets(ts[i:]):
                yield comp2(C, 0, l, r)

def fold_4cells():
    ps = list(brackets(P_edges(3, 0, 3)))[:5]
    A, B, Cc, D, E = ps
    k = kap
    mABC = struct_cell(C, comp2(C, 1, k(A, B), k(B, Cc)), k(A, Cc))
    mACD = struct_cell(C, comp2(C, 1, k(A, Cc), k(Cc, D)), k(A, D))
    mBCD = struct_cell(C, comp2(C, 1, k(B, Cc), k(Cc, D)), k(B, D))
    mABD = struct_cell(C, comp2(C, 1, k(A, B), k(B, D)), k(A, D))
    src = comp2(C, 1, comp2(C, 1, k(A, B), k(B, Cc)), k(Cc, D))
    assoc = struct_cell(C, src, comp2(C, 1, k(A, B), comp2(C, 1, k(B, Cc), k(Cc, D))))
    r1 = comp2(C, 2, comp2(C, 1, mABC, k(Cc, D)), mACD)
    r2 = comp2(C, 2, comp2(C, 2, assoc, comp2(C, 1, k(A, B), mBCD)), mABD)
    overlap = struct_cell(C, r1, r2)
    # disjoint pairs: interchange on V(1,1)
    V = tree_ctx(((((),), ((),)),))
    twos = [i for i, T_ in enumerate(V) if tdim(T_) == 1]
    h1, h2 = [i for i, T_ in enumerate(V) if tdim(T_) == 2]
    a0, a1, b0, b1 = V[h1][2], V[h1][3], V[h2][2], V[h2][3]
    rr1 = comp2(V, 2, comp2(V, 1, v(h1), b0), comp2(V, 1, a1, v(h2)))
    rr2 = comp2(V, 2, comp2(V, 1, a0, v(h2)), comp2(V, 1, v(h1), b1))
    inter = ('coh', V, arr(infer(V, rr1), rr1, rr2), tuple(v(i) for i in range(len(V))))
    mCDE = struct_cell(C, comp2(C, 1, k(Cc, D), k(D, E)), k(Cc, E))
    sig = sub_from(V, C, {h1: mABC, h2: mCDE})
    disjoint = subst_tm(inter, sig)
    infer(C, overlap); infer(C, disjoint)
    return dict(overlap=overlap, disjoint=disjoint)

# ---------------------------------------------------------------- generated terms and frames
def gen_terms(rng, n):
    out = []
    for (a, b) in [(0, 3), (0, 2), (1, 3), (0, 1)]:
        for i in range(a + 1, b + 1):
            out.append(letter(i, a, b))
    full = [(r, s) for r in range(1, K + 1) for s in range(0, r)]
    for (r, s) in full:
        w = tuple(range(r, s, -1))
        A = lnest(P_edges(r, 0, K)); B = lnest(P_edges(s, 0, K))
        out.append(N(w, A, B, 0, K))
    while len(out) < n:
        t = rng.choice(out)
        A_ = infer(C, t)
        a0, b0 = A_[1][2][1], A_[1][3][1]
        r = rng.random()
        if r < 0.3:
            t = comp2(C, 0, ident(C, a0), t)
        elif r < 0.6:
            t = comp2(C, 0, t, ident(C, b0))
        else:
            s1 = A_[2]
            alt = comp2(C, 0, ident(C, a0), s1)
            t = comp2(C, 1, kap(alt, s1), t)
        out.append(t)
    return out

def main(n=50, seed=7):
    rng = random.Random(seed)
    # normal forms for every word between the outer endpoints x0-, x3+
    nfs = []
    for (a, b) in [(0, 3), (1, 3), (0, 2)]:
        for r in range(a, b + 1):
            for s in range(a, r + 1):
                w = tuple(range(r, s, -1))
                A = lnest(P_edges(r, a, b)) if len(P_edges(r, a, b)) > 1 else P_edges(r, a, b)[0]
                B = rnest(P_edges(s, a, b))
                nfs.append(((a, b, w), N(w, A, B, a, b)))
    boxed = [t for (key, t) in nfs if key == (0, 3, (3, 2, 1))][0]
    assert len(N_list((3, 2, 1), lnest(P_edges(3, 0, 3)), rnest(P_edges(0, 0, 3)), 0, 3)) == 7
    # multiplications for every split of every word on (0,3)
    mus = []
    for r in range(0, K + 1):
        for s in range(0, r + 1):
            for t_ in range(s, r + 1):
                u = tuple(range(r, t_, -1)); v_ = tuple(range(t_, s, -1))
                A = lnest(P_edges(r, 0, K)); B = rnest(P_edges(t_, 0, K))
                Cc = lnest(P_edges(s, 0, K))
                m_, ty = mu(u, v_, A, B, Cc, 0, K)
                mus.append(((u, v_), m_, ty))
    f4 = fold_4cells()
    # frames
    facts = []
    seen = set()
    for t in gen_terms(rng, n):
        if t in seen or t[0] != 'coh': continue
        seen.add(t)
        R, d, eta, H = factor_cols(C, t)
        _, P, A, g = t
        cols = column_ranges(tree_of(P))
        act = [j for j, (s0, s1, f, e) in enumerate(cols)
               if any(two(C, g[i]) for i in range(f, e))]
        assert len(act) == 1, 'forced word: expected one active column, got %s' % act
        R2, d2, e2, H2 = factor_cols(R, H)
        assert R2 == R and H2 == H, 'stability'
        facts.append((t, R, d, eta, H))
    print('chain k=%d: normal forms %d, multiplications %d, fold 4-cells %d, frames %d'
          % (K, len(nfs), len(mus), len(f4), len(facts)))
    return nfs, boxed, mus, f4, facts

def emit_module():
    from emit_agda import Emitter
    nfs, boxed, mus, f4, facts = main()
    E = Emitter()
    E.check_typed('ctx-letters', C, letter(2, 0, 3))
    for i, (key, t) in enumerate(nfs):
        E.check_typed('N%d' % i, C, t)
    E.check_typed('boxed', C, boxed)
    for i, (key, m_, ty) in enumerate(mus):
        E.check_type('mu%d' % i, C, m_, ty)
    for k_, t in f4.items():
        E.check_typed('fold4-' + k_, C, t)
    for i, (T_, R, d, e, H) in enumerate(facts):
        E.check_typed('H%d' % i, R, H)
        E.check_typed('eta%d' % i, C, eta_witness(R, e))
        E.check_eq('fact%d' % i, H, e, T_)
    src = E.module('CaTTExp.Generated.ChainCylinderRC3',
                   'Checks toward RC(3) on the full cylinder of the chain x0 -> x1 -> x2 -> x3 (round-5 answer): raw letters, normal forms N_w (including the boxed three-letter form), the multiplication mu for every split, the fold 4-cells, and frame factorisations. Built by tools/rc3_chain.py.')
    open('../src/CaTTExp/Generated/ChainCylinderRC3.agda', 'w').write(src)
    print('emitted', len(E.defs), 'definitions,', len(E.checks), 'checks')

if __name__ == '__main__':
    import sys
    if sys.argv[1:] == ['emit']:
        emit_module()
    else:
        main()
