"""
RC(3) on the cylinder of x -> y -> z with Y = {x, f, g}: the smallest case in
which two generator letters can be exchanged (relative-coherence.md §7.6).

    W:  x-, x+ : *,  X : x- -> x+,  y, z : *,
        f- : x- -> y,  f+ : x+ -> y,  F : f- => X *0 f+,
        g-, g+ : y -> z,  G : g- => g+.

y is unselected, so it is a cut vertex: W = W1 v_y W2 with W1 the
single-letter part (x-, x+, X, y, f-, f+, F) and W2 = D^2 (y, z, g-, g+, G).

We check on generated terms:
  * the cut-vertex column lemma: for a term with 0-boundary crossing y,
    the images of the arity's 0-vertices are monotone, and either some vertex
    goes to y (split) and no column crosses, or exactly one column crosses y;
    on each side of a split there is at most one active column;
  * literal factorisation through the retained frame, with one or two
    retained columns, gamma = delta[eta], H typed over R, and stability;
  * the exchange coherences chi_L, chi_R and a 4-term between the two
    3-terms that relate the two exchange orders;
  * the horizontal fold mu^h (interchange) on normal forms;
  * frame normalisers v_H : H => kappa . (N_left *0 N_right) . kappa over R,
    and their instances v_H[eta] in W.
Everything is re-checked by catt.infer here and by the certified Agda
checker in src/CaTTExp/Generated/WedgeRC3.agda.
"""
import random
from catt import *
from rc2 import struct_cell, ident, path, rename, lfold
from rc3_square import column_ranges

# ---------------------------------------------------------------- the context W
XM, XP, XU, YV, ZV, FM, FP, FF, GM, GP, GG = range(11)
_W7 = (STAR, STAR, arr(STAR, v(XM), v(XP)), STAR, STAR,
       arr(STAR, v(XM), v(YV)), arr(STAR, v(XP), v(YV)))
XF = comp2(_W7, 0, v(XU), v(FP))
_W8 = _W7 + (arr(arr(STAR, v(XM), v(YV)), v(FM), XF),)
W = _W8 + (arr(STAR, v(YV), v(ZV)), arr(STAR, v(YV), v(ZV)),
           arr(arr(STAR, v(YV), v(ZV)), v(GM), v(GP)))
check_ctx(W)
RANK = {XM: 0, XP: 1, YV: 2, ZV: 3}

def kap(G, a, b): return struct_cell(G, a, b)
def c0(a, b): return comp2(W, 0, a, b)
def c1(a, b): return comp2(W, 1, a, b)

def two(G, t):
    return any(tdim(G[i]) >= 1 for i in fv_tm(t))

def zero_bd(G, t):
    A = infer(G, t)
    while tdim(A) > 0:
        A = A[1]
    return A[2][1], A[3][1]

# ---------------------------------------------------------------- the column lemma
def column_report(G, T, rank):
    """For T = coh_{P,A}[g] crossing the cut (rank 2): check monotonicity, the
    split / single crossing column dichotomy, and <= 1 active column per side.
    Returns 'split' or 'cross'."""
    _, P, A, g = T
    cols = column_ranges(tree_of(P))
    verts = [g[0][1]] + [g[s1][1] for (_, s1, _, _) in cols]
    rs = [rank[x] for x in verts]
    assert all(a <= b for a, b in zip(rs, rs[1:])), 'not monotone'
    split = 2 in rs
    crossing = [j for j, (s0, s1, _, _) in enumerate(cols)
                if rank[g[s0][1]] < 2 < rank[g[s1][1]]]
    if split:
        assert not crossing
        left = [j for j, (s0, s1, f, e) in enumerate(cols)
                if rank[g[s1][1]] <= 2 and any(two(G, g[i]) for i in range(f, e))]
        right = [j for j, (s0, s1, f, e) in enumerate(cols)
                 if rank[g[s0][1]] >= 2 and any(two(G, g[i]) for i in range(f, e))]
        assert len(left) <= 1 and len(right) <= 1, 'two active columns on one side'
        for j in left:
            assert (g[cols[j][0]], g[cols[j][1]]) == (v(XM), v(YV)), 'left active not x- -> y'
        for j in right:
            assert (g[cols[j][0]], g[cols[j][1]]) == (v(YV), v(ZV)), 'right active not y -> z'
        return 'split'
    assert len(crossing) == 1, 'crossing columns: %s' % crossing
    j = crossing[0]
    for k, (s0, s1, f, e) in enumerate(cols):
        if k != j:
            assert not any(two(G, g[i]) for i in range(f, e)), 'active non-crossing column'
    return 'cross'

def subterms(t):
    if t[0] == 'v':
        return
    yield t
    for u in t[3]:
        yield from subterms(u)

# ---------------------------------------------------------------- factorisation with several retained columns
def factor_cols(G, T):
    """Retain every active column (one containing a 2-variable entry); pull each
    inactive column back to the chain of its path.  Returns (R, d, eta, H)
    with g = d[eta] syntactically and H = coh_{P,A}[d] a term of R."""
    _, P, A, g = T
    tree = tree_of(P)
    cols = column_ranges(tree)
    active = {j for j, (s0, s1, f, end) in enumerate(cols)
              if any(two(G, g[i]) for i in range(f, end))}
    Rtree, d, eta = [], [None] * len(P), [g[0]]
    d[0] = v(0)
    cur, nR = 0, 1
    for j, (s0, s1, f, end) in enumerate(cols):
        if j in active:
            Rtree.append(tree[j])
            ycol = nR
            d[s1] = v(ycol)
            eta.append(g[s1])
            for k, i in enumerate(range(f, end)):
                d[i] = v(ycol + 1 + k)
                eta.append(g[i])
            nR = ycol + 1 + (end - f)
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
                d[i] = rename(g[i], ren)
            d[s1] = v(cur)
    R = tree_ctx(tuple(Rtree))
    d, eta = tuple(d), tuple(eta)
    assert len(eta) == len(R)
    H = ('coh', P, A, d)
    assert tuple(subst_tm(u, eta) for u in d) == g, 'g != d[eta]'
    infer(R, H)
    return R, d, eta, H

# ---------------------------------------------------------------- generated 2-terms
def base_terms():
    gm, gp, fm = v(GM), v(GP), v(FM)
    out = [
        c0(v(FF), gm), c0(v(FF), gp),                 # F whiskered by g-, g+
        c0(fm, v(GG)), c0(XF, v(GG)),                 # G whiskered by f-, X f+
        c0(v(XU), c0(v(FP), v(GG))),                  # X (f+ G): crossing column, path column
        c0(v(FF), v(GG)),                             # F *0 G (split)
    ]
    T1 = c1(c0(v(FF), gm), c0(XF, v(GG)))             # first F, then G
    T2 = c1(c0(fm, v(GG)), c0(v(FF), gp))             # first G, then F
    out += [T1, T2]
    return out

def gen_terms(rng, n):
    base = base_terms()
    out = list(base)
    while len(out) < n:
        t = rng.choice(out)
        r = rng.random()
        a, b = zero_bd(W, t)
        if r < 0.25 and b != ZV:
            continue
        if r < 0.25:
            t = c0(t, ident(W, ZV))
        elif r < 0.5 and a == XM:
            t = c0(ident(W, XM), t)
        elif r < 0.75:
            s1 = infer(W, t)[2]
            w, x0, x1 = path(W, s1)
            alt = c0(ident(W, x0), s1)
            t = c1(kap(W, alt, s1), t)
        else:
            t1 = infer(W, t)[3]
            w, x0, x1 = path(W, t1)
            alt = c0(t1, ident(W, x1))
            t = c1(t, kap(W, t1, alt))
        out.append(t)
    return out

# ---------------------------------------------------------------- the exchange
P2 = tree_ctx((((),), ((),)))      # D^2 *0 D^2: x, y1, a, a', al, y2, b, b', be
def exchange_terms():
    a, a_, al, b, b_, be = v(2), v(3), v(4), v(6), v(7), v(8)
    s1 = comp2(P2, 1, comp2(P2, 0, al, b), comp2(P2, 0, a_, be))   # F first
    s2 = comp2(P2, 1, comp2(P2, 0, a, be), comp2(P2, 0, al, b_))   # G first
    h = comp2(P2, 0, al, be)
    A = infer(P2, h)
    chiL = ('coh', P2, arr(A, s1, h), tuple(v(i) for i in range(len(P2))))
    chiRi = ('coh', P2, arr(A, h, s2), tuple(v(i) for i in range(len(P2))))
    psi1 = comp2(P2, 2, chiL, chiRi)
    psi2 = ('coh', P2, arr(A, s1, s2), tuple(v(i) for i in range(len(P2))))
    B = infer(P2, psi1)
    assert B == infer(P2, psi2)
    four = ('coh', P2, arr(B, psi1, psi2), tuple(v(i) for i in range(len(P2))))
    sig = sub_from(P2, W, {4: v(FF), 8: v(GG)})
    inst = {k: subst_tm(t, sig) for k, t in
            dict(chiL=chiL, chiRi=chiRi, psi1=psi1, psi2=psi2, four=four).items()}
    for t in inst.values():
        infer(W, t)
    T1, T2 = base_terms()[-2:]
    assert subst_tm(s1, sig) == T1 and subst_tm(s2, sig) == T2
    return inst

# ---------------------------------------------------------------- horizontal fold mu^h
P22 = tree_ctx((((), ()), ((), ())))
def mu_h_instance():
    # P22: x, y1, u0, u1, z1, u2, z2, y2, w0, w1, q1, w2, q2
    z1, z2, q1, q2 = v(4), v(6), v(10), v(12)
    src = comp2(P22, 1, comp2(P22, 0, z1, q1), comp2(P22, 0, z2, q2))
    tgt = comp2(P22, 0, comp2(P22, 1, z1, z2), comp2(P22, 1, q1, q2))
    A = infer(P22, src)
    mu = ('coh', P22, arr(A, src, tgt), tuple(v(i) for i in range(len(P22))))
    infer(P22, mu)
    # instance: the two layers of T1 split: (F *0 k_{g-}) . (k_{Xf+} *0 G)
    kg = kap(W, v(GM), v(GM))
    kx = kap(W, XF, XF)
    sig = sub_from(P22, W, {4: v(FF), 6: kx, 10: kg, 12: v(GG)})
    inst = subst_tm(mu, sig)
    infer(W, inst)
    return mu, inst

# ---------------------------------------------------------------- frame normalisers
def frame_nf(R, H):
    """Over a frame R (columns: vertical chains or single edges), the horizontal
    normal form kappa(sH, u) . (N_1 *0 ... *0 N_c) . kappa(u', tH), where N_j
    is the left fold of the column's 2-variables (or the identity path cell
    on a 1-dimensional column).  Returns v_H : H => NF over R, or None if H
    is not full in R."""
    if fv_tm(H) | fv_ty(infer(R, H)) != frozenset(range(len(R))):
        return None
    tree = tree_of(R)
    cols = column_ranges(tree)
    pieces, srcs, tgts = [], [], []
    for (s0, s1, f, end) in cols:
        twos = [i for i in range(f, end) if tdim(R[i]) == 1]
        if twos:
            pieces.append(lfold(R, 1, [v(i) for i in twos]))
            srcs.append(R[twos[0]][2]); tgts.append(R[twos[-1]][3])
        else:
            pieces.append(kap(R, v(f), v(f)))
            srcs.append(v(f)); tgts.append(v(f))
    def r0(ts):
        t = ts[-1]
        for u in reversed(ts[:-1]):
            t = comp2(R, 0, u, t)
        return t
    mid = r0(pieces)
    u0, u1 = r0(srcs), r0(tgts)
    sH, tH = infer(R, H)[2], infer(R, H)[3]
    nf = comp2(R, 1, comp2(R, 1, kap(R, sH, u0), mid), kap(R, u1, tH))
    A = infer(R, H)
    vH = ('coh', R, arr(A, H, nf), tuple(v(i) for i in range(len(R))))
    infer(R, vH)
    return vH

# ---------------------------------------------------------------- run
def main(n=60, seed=5):
    rng = random.Random(seed)
    seen, facts, kinds = set(), [], {'split': 0, 'cross': 0}
    nsub = 0
    for T in gen_terms(rng, n):
        if T in seen: continue
        seen.add(T)
        for u in subterms(T):
            if tdim(infer(W, u)) < 0: continue
            a, b = zero_bd(W, u)
            if RANK[a] < 2 < RANK[b]:
                kinds[column_report(W, u, RANK)] += 1
                nsub += 1
        if two(W, T) and T[0] == 'coh':
            R, d, eta, H = factor_cols(W, T)
            R2, d2, e2, H2 = factor_cols(R, H)
            assert R2 == R and H2 == H, 'stability (H over R)'
            facts.append((T, R, d, eta, H))
    # stability under composition with a path cell over R
    stab = 0
    for (T, R, d, eta, H) in facts[:15]:
        t1 = infer(R, H)[3]
        w, a, b = path(R, t1)
        alt = comp2(R, 0, t1, ident(R, b))
        u = comp2(R, 1, H, struct_cell(R, t1, alt))
        Ru, du, eu, Hu = factor_cols(R, u)
        Rs, ds, es, Hs = factor_cols(W, subst_tm(u, eta))
        assert Ru == Rs and Hu == Hs, 'stability (u over R)'
        stab += 1
    vHs = []
    for (T, R, d, eta, H) in facts:
        vH = frame_nf(R, H)
        if vH is not None:
            inst = subst_tm(vH, eta)
            assert infer(W, inst)[2] == T
            vHs.append((T, R, eta, vH, inst))
    ex = exchange_terms()
    mu, mu_inst = mu_h_instance()
    # 3- and 4-dimensional arities: the column lemma and factorisation
    for t in list(ex.values()) + [mu_inst]:
        for u in subterms(t):
            if tdim(infer(W, u)) < 0: continue
            a, b = zero_bd(W, u)
            if RANK[a] < 2 < RANK[b]:
                kinds[column_report(W, u, RANK)] += 1
                nsub += 1
        R, d, eta, H = factor_cols(W, t)
        facts.append((t, R, d, eta, H))
    print('wedge: crossing subterms', nsub, kinds, ' factorisations', len(facts),
          ' stability', stab, ' frame normalisers', len(vHs), ' exchange + mu^h ok')
    return facts, vHs, ex, (mu, mu_inst)

def eta_witness(R, e):
    u = ucomp(R)
    return ('coh', R, arr(infer(R, u), u, u), tuple(e))

def emit_module():
    from emit_agda import Emitter
    facts, vHs, ex, (mu, mu_inst) = main()
    E = Emitter()
    for i, (T, R, d, e, H) in enumerate(facts):
        E.check_typed('T%d' % i, W, T)
        E.check_typed('H%d' % i, R, H)
        E.check_typed('eta%d' % i, W, eta_witness(R, e))
        E.check_eq('fact%d' % i, H, e, T)
    for i, (T, R, e, vH, inst) in enumerate(vHs):
        E.check_typed('vH%d' % i, R, vH)
        E.check_eq('vHinst%d' % i, vH, e, inst)
        E.check_typed('vHW%d' % i, W, inst)
    for k, t in ex.items():
        E.check_typed('ex-' + k, W, t)
    E.check_typed('muh', P22, mu)
    E.check_typed('muh-inst', W, mu_inst)
    src = E.module('CaTTExp.Generated.WedgeRC3',
                   'RC(3) for the cylinder of x -> y -> z with Y = {x, f, g} (relative-coherence.md §7.6): factorisations through one- and two-column frames, frame normalisers, the exchange coherences and a 4-term between the two exchange routes, and the horizontal fold. Built by tools/rc3_wedge.py.')
    open('../src/CaTTExp/Generated/WedgeRC3.agda', 'w').write(src)
    print('emitted', len(E.defs), 'definitions,', len(E.checks), 'checks')

def emit_negative():
    """Negative control: the exchange 3-term psi1 at its type with source and
    target swapped.  Agda must reject src/CaTTExp/Generated/NegWedge.agda."""
    from emit_agda import Emitter
    t = exchange_terms()['psi1']; A = infer(W, t)
    E = Emitter(); E.check_type('bad', W, t, arr(A[1], A[3], A[2]))
    open('../src/CaTTExp/Generated/NegWedge.agda', 'w').write(
        E.module('CaTTExp.Generated.NegWedge', 'Negative control: must be rejected.'))

if __name__ == '__main__':
    import sys
    if sys.argv[1:] == ['emit']:
        emit_module()
    elif sys.argv[1:] == ['neg']:
        emit_negative()
    else:
        main()
