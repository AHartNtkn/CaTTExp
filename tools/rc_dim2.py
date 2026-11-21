"""
Theorem A (RC(2)) with smaller answers.

Same construction as tools/rc2.py (whose functions it reuses), with one
change in the exchange step: the two windows produced by Lemma E are put in
canonical form directly, item by item (Lemma G(ii) for each column
coherence, Lemma P for each run of 2-terms without 2-variables), instead of
running the general normalization on them. The general normalization nests
functoriality cells and makes each exchange cost ~10^5 nodes; the direct
route costs a few coherences per item.

Untrusted, like rc2.py: every term is re-checked by catt.infer here and by
the certified checker in the emitted tables.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from catt import *
import rc2
from rc2 import (rcomp, has2, functor, abstract_whisker, maximal_vars, rename, Pg_tree, NF, Pg_info, H_over, N_over, kappa, lfold, vc3, reassoc, flat_shape,
                 functor_column, canon, canon_term, normalize, real, item_term,
                 path, tree_labels, E_info, column_into, swap_split, src, tgt)

def _tree(P):
    return tree_of(P)

def column_shape(P):
    """If P is a column pasting context (chain, one 2-disc, chain), return
    (a, b): the lengths of the two chains."""
    t = tree_of(P)
    if t is None:
        return None
    ks = [i for i, c in enumerate(t) if c != ()]
    if len(ks) != 1 or t[ks[0]] != ((),):
        return None
    return ks[0], len(t) - ks[0] - 1

def _pull_map(G, a, off, vp, ep):
    """A 1-term a of G whose path occupies chain positions [off, off+len),
    rewritten over a context whose position p vertex is vp(p) and edge ep(p)."""
    if a[0] == 'v':
        return v(ep(off))
    _, P, A, s = a
    if ps_dim(P) == 0:
        return ('coh', P, A, (v(vp(off)),))
    out = [None] * len(P)
    pos = off
    out[0] = v(vp(pos))
    for i, B in enumerate(P):
        if i == 0 or tdim(B) + 1 == 0:
            continue
        out[i] = _pull_map(G, s[i], pos, vp, ep)
        pos += len(path(G, s[i])[0])
        out[B[3][1]] = v(vp(pos))
    return ('coh', P, A, tuple(out))

def lemma_g2(G, W):
    """W = coh_{P'}[theta'] with P' a column context and theta'(Z) a
    2-variable x. Returns (g, items, fwd, bwd) with items the canonical
    [kappa, H_g, kappa] and fwd : W => lfold(items), bwd back (Lemma G(ii))."""
    _, Pp, Ap, th = W
    a, b = column_shape(Pp)
    labp = tree_labels(_tree(Pp))
    Zp = labp[('f', (a, 0))]
    x = th[Zp]
    assert x[0] == 'v'
    pre_terms = [th[labp[('f', (i,))]] for i in range(a)]
    suf_terms = [th[labp[('f', (a + 1 + j,))]] for j in range(b)]
    lam = tuple(e for t in pre_terms for e in path(G, t)[0])
    rho = tuple(e for t in suf_terms for e in path(G, t)[0])
    g = (lam, x[1], rho)
    nl, nr = len(lam), len(rho)
    P, pre, zm, zp, Z, suf = Pg_info(nl, nr)
    lab = tree_labels(rc2.Pg_tree(nl, nr))
    def vp(p):
        return 0 if p == 0 else lab[('y', (p - 1,))]
    def ep(p):
        return lab[('f', (p,))]
    sig = [None] * len(Pp)
    sig[0] = v(0)
    off = 0
    for i in range(a):
        e = labp[('f', (i,))]
        sig[e] = _pull_map(G, pre_terms[i], off, vp, ep)
        off += len(path(G, pre_terms[i])[0])
        sig[labp[('y', (i,))]] = v(vp(off))
    sig[labp[('f', (a,))]] = v(zm)
    sig[labp[('y', (a, 0))]] = v(zp)
    sig[Zp] = v(Z)
    off = nl + 1
    sig[labp[('y', (a,))]] = v(vp(off))
    for j in range(b):
        e = labp[('f', (a + 1 + j,))]
        sig[e] = _pull_map(G, suf_terms[j], off, vp, ep)
        off += len(path(G, suf_terms[j])[0])
        sig[labp[('y', (a + 1 + j,))]] = v(vp(off))
    Wp = ('coh', Pp, Ap, tuple(sig))
    thg = rc2.theta(G, g)
    assert subst_tm(Wp, thg) == W, 'lemma_g2: pull-back mismatch'
    Hp = H_over(nl, nr)
    k1 = kappa(P, src(P, Wp), src(P, Hp))
    k2 = kappa(P, tgt(P, Hp), tgt(P, Wp))
    tgtP = lfold(P, 1, [k1, Hp, k2])
    A = infer(P, Wp)
    fwd = ('coh', P, arr(A, Wp, tgtP), thg)
    bwd = ('coh', P, arr(A, tgtP, Wp), thg)
    items = [('S', subst_tm(k1, thg)), ('H', g), ('S', subst_tm(k2, thg))]
    assert real(G, items) == subst_tm(tgtP, thg)
    return g, items, fwd, bwd

def is_column_coh(G, t):
    if t[0] != 'coh':
        return False
    sh = column_shape(t[1])
    if sh is None or ps_dim(t[1]) != 2:
        return False
    lab = tree_labels(tree_of(t[1]))
    Z = lab[('f', (sh[0], 0))]
    return t[3][Z][0] == 'v' and tdim(G[t[3][Z][1]]) == 1

def nf_from_items(G, items):
    """items: 2-terms, each without 2-variables or a column coherence on a
    2-variable. Returns NF(flat, fwd, bwd) with fwd : lfold(items) =>
    real(flat)."""
    groups, cf, cb = [], [], []
    for t in items:
        if is_column_coh(G, t):
            g, its, f, b = lemma_g2(G, t)
            groups.append(its); cf.append(f); cb.append(b)
        else:
            assert not rc2.has2(G, t), 'nf_from_items: unexpected 2-variable'
            groups.append([('S', t)]); cf.append(None); cb.append(None)
    f1 = functor_column(G, items, cf)
    expanded = [real(G, grp) for grp in groups]
    b1 = functor_column(G, expanded, cb)
    flat = [it for grp in groups for it in grp]
    shape, off = [], 0
    for grp in groups:
        shape.append(flat_shape(len(grp), off)); off += len(grp)
    terms = [item_term(G, it) for it in flat]
    f2, b2 = reassoc(G, terms, shape, flat_shape(len(flat)))
    return NF(flat, vc3(G, [f1, f2]), vc3(G, [b2, b1]))

def exchange_window(G, g1, g2, a_prev, b_next):
    """Lemma E as in rc2.exchange_cell, returning also the item lists of the
    two windows."""
    right_first = len(g1[0]) > len(g2[0])
    left, right = (g2, g1) if right_first else (g1, g2)
    lam, mu, rho = swap_split(G, left, right, right_first)
    x, y = left[1], right[1]
    P, pre, (z1m, z1p, Z1), mid, (z2m, z2p, Z2), suf = E_info(len(lam), len(mu), len(rho))
    V_ = lambda ls: [v(e) for e in ls]
    H1 = column_into(P, len(pre), len(mid) + 1 + len(suf), V_(pre), Z1, V_(mid) + [v(z2m)] + V_(suf))
    H2 = column_into(P, len(pre) + 1 + len(mid), len(suf), V_(pre) + [v(z1p)] + V_(mid), Z2, V_(suf))
    H2b = column_into(P, len(pre) + 1 + len(mid), len(suf), V_(pre) + [v(z1m)] + V_(mid), Z2, V_(suf))
    H1b = column_into(P, len(pre), len(mid) + 1 + len(suf), V_(pre), Z1, V_(mid) + [v(z2p)] + V_(suf))
    Sc = rc2.rcomp(P, V_(pre) + [v(z1m)] + V_(mid) + [v(z2m)] + V_(suf))
    Tc = rc2.rcomp(P, V_(pre) + [v(z1p)] + V_(mid) + [v(z2p)] + V_(suf))
    I1 = [kappa(P, Sc, src(P, H1)), H1, kappa(P, tgt(P, H1), src(P, H2)), H2, kappa(P, tgt(P, H2), Tc)]
    I2 = [kappa(P, Sc, src(P, H2b)), H2b, kappa(P, tgt(P, H2b), src(P, H1b)), H1b, kappa(P, tgt(P, H1b), Tc)]
    TE, TEb = lfold(P, 1, I1), lfold(P, 1, I2)
    A = infer(P, TE)
    im = {Z1: v(x), Z2: v(y)}
    for e, ge in zip(pre, lam): im[e] = v(ge)
    for e, ge in zip(mid, mu): im[e] = v(ge)
    for e, ge in zip(suf, rho): im[e] = v(ge)
    th = sub_from(P, G, im)
    e_f = ('coh', P, arr(A, TE, TEb), th)
    e_b = ('coh', P, arr(A, TEb, TE), th)
    t1, t2 = subst_tm(TE, th), subst_tm(TEb, th)
    ka, kb = kappa(G, a_prev, src(G, t1)), kappa(G, tgt(G, t1), b_next)
    it1 = [ka] + [subst_tm(t, th) for t in I1] + [kb]
    it2 = [ka] + [subst_tm(t, th) for t in I2] + [kb]
    def wrap(cell):
        return comp2(G, 1, comp2(G, 1, ka, cell), kb)
    if right_first:
        return it2, it1, wrap(e_b), wrap(e_f)
    return it1, it2, wrap(e_f), wrap(e_b)

WINDOW_SHAPE = [0, [1, 2, 3, 4, 5], 6]

def window_nf(G, items):
    """NF of the window lfold([ka, lfold(5 items), kb]) (its literal bracketing)."""
    nf = nf_from_items(G, items)
    f0, b0 = reassoc(G, items, WINDOW_SHAPE, flat_shape(len(items)))
    return NF(nf.items, vc3(G, [f0, nf.fwd]), vc3(G, [nf.bwd, b0]))

def swap_in_canon_fast(G, gens, i, A, B):
    items = canon_term(G, gens, A, B)
    g1, g2 = gens[i], gens[i + 1]
    a_prev = A if i == 0 else rc2.N_term(G, gens[i - 1], '+')
    b_next = B if i + 2 == len(gens) else rc2.N_term(G, gens[i + 2], '-')
    it1, it2, ef, eb = exchange_window(G, g1, g2, a_prev, b_next)
    nZ, nZ2 = window_nf(G, it1), window_nf(G, it2)
    gz, cz, fz, bz = canon(G, nZ, a_prev, b_next)
    gz2, cz2, fz2, bz2 = canon(G, nZ2, a_prev, b_next)
    assert gz == [g1, g2], (gz, [g1, g2])
    new = list(gens); new[i], new[i + 1] = gz2[0], gz2[1]
    window_f = vc3(G, [bz, ef, fz2])
    window_b = vc3(G, [bz2, eb, fz])
    items2 = canon_term(G, new, A, B)
    w0 = 2 * i
    shape = list(range(w0)) + [list(range(w0, w0 + 5))] + list(range(w0 + 5, len(items)))
    r1f, r1b = reassoc(G, items, flat_shape(len(items)), shape)
    r2f, r2b = reassoc(G, items2, flat_shape(len(items2)), shape)
    grouped = items[:w0] + [lfold(G, 1, items[w0:w0 + 5])] + items[w0 + 5:]
    grouped2 = items2[:w0] + [lfold(G, 1, items2[w0:w0 + 5])] + items2[w0 + 5:]
    assert grouped[w0] == cz and grouped2[w0] == cz2
    cells = [None] * len(grouped); cells[w0] = window_f
    cellsb = [None] * len(grouped2); cellsb[w0] = window_b
    mf = functor_column(G, grouped, cells)
    mb = functor_column(G, grouped2, cellsb)
    return new, vc3(G, [r1f, mf, r2b]), vc3(G, [r2f, mb, r1b])

def rc2_small(G, T, U):
    nT, nU = normalize_top(G, T), normalize_top(G, U)
    A, B = src(G, T), tgt(G, T)
    gT, cT, fT, bT = canon(G, nT, A, B)
    gU, cU, fU, bU = canon(G, nU, A, B)
    fwd, cur = [fT], list(gT)
    target = [g[1] for g in gU]
    for pos, x in enumerate(target):
        j = next(k for k in range(pos, len(cur)) if cur[k][1] == x)
        while j > pos:
            cur, f, b = swap_in_canon_fast(G, cur, j - 1, A, B)
            fwd.append(f); j -= 1
    assert cur == gU, (cur, gU)
    fwd.append(bU)
    K = vc3(G, fwd)
    assert infer(G, K) == arr(infer(G, T), T, U)
    return K

# ---------------------------------------------------------------- sequentialization without functoriality cells for variable arguments

def normalize_small(G, T):
    """Returns NF with fwd: T => real(items), bwd: real(items) => T."""
    if not has2(G, T):
        return NF([('S', T)], None, None)
    if T[0] == 'v' and False:
        g = ((), T[1], ())
        W, items, f, b = abstract_whisker(G, None, g, None)
        # W = H_g[theta]; compare the variable x with W over the disc
        P, pre, zm, zp, Z, suf = Pg_info(0, 0)
        Hp = H_over(0, 0)
        A = infer(P, v(Z))
        th = theta(G, g)
        c1 = ('coh', P, arr(A, v(Z), Hp), th)
        c1r = ('coh', P, arr(A, Hp, v(Z)), th)
        return NF(items, vc3(G, [c1, f]), vc3(G, [b, c1r]))
    _, P, A, gam = T
    assert ps_dim(P) == 2
    tree = tree_of(P)
    lab = tree_labels(tree)
    inv = {vv: k for k, vv in lab.items()}
    two = [i for i in range(len(P)) if tdim(P[i]) == 1]
    sub_nf = {a: (NF([('X', gam[a][1])], None, None) if gam[a][0] == 'v' else normalize_small(G, gam[a])) for a in two}
    # step 1: functoriality T => coh_P[gam']
    base = {i: gam[i] for i in maximal_vars(P)}
    body = ('coh', P, A, tuple(v(i) for i in range(len(P))))
    f1 = functor(G, None, P, tree, body, base, {a: n.fwd for a, n in sub_nf.items() if n.fwd is not None})
    gam2 = dict(base);
    for a, n in sub_nf.items(): gam2[a] = real_x(G, n.items)
    b1 = functor(G, None, P, tree, body, gam2, {a: n.bwd for a, n in sub_nf.items() if n.bwd is not None})
    # step 2: subdivide each 2-var into its items
    m = {a: len(sub_nf[a].items) for a in two}
    def sub_tree(node, prefix, depth):
        out = []
        for i, child in enumerate(node):
            p = prefix + (i,)
            if depth == 1:
                # children of a 1-cell slot are 2-cells (leaves)
                new = []
                for j, c2 in enumerate(child):
                    a = lab[('f', p + (j,))]
                    new += [()] * m[a]
                out.append(tuple(new))
            else:
                out.append(sub_tree(child, p, depth + 1))
        return tuple(out)
    tree2 = sub_tree(tree, (), 1)
    P2 = tree_ctx(tree2)
    lab2 = tree_labels(tree2)
    zeta = [None] * len(P)
    beta_img = {}
    for i in range(len(P)):
        k = inv[i]
        if k == ('x',) or len(k[1]) == 1:
            zeta[i] = v(lab2[k])
    for (kind, p), vv in list(lab.items())[1:]:
        if len(p) == 2:
            col, j = p
            a = lab[('f', p)]
            start = sum(m[lab[('f', (col, jj))]] for jj in range(j))
            bs = [lab2[('f', (col, start + t))] for t in range(m[a])]
            if kind == 'f':
                zeta[a] = lfold(P2, 1, [v(b) for b in bs])
                for b, it in zip(bs, sub_nf[a].items):
                    beta_img[b] = item_term_x(G, it)
            else:  # target 1-cell of the 2-var at p
                zeta[vv] = v(lab2[('y', (col, start + m[a] - 1))])
    zeta = tuple(zeta)
    cohz = ('coh', P, A, zeta)
    maxim2 = {}
    for i in maximal_vars(P2):
        if i in beta_img:
            maxim2[i] = beta_img[i]
        else:
            k = None
            for kk, vv in lab2.items():
                if vv == i: k = kk
            # a bare 1-cell column: same path in P
            maxim2[i] = gam[lab[k]]
    g2 = sub_from(P2, G, maxim2)
    Tp = ('coh', P, A, tuple(subst_tm(z, g2) for z in zeta))
    assert subst_tm(cohz, g2) == ('coh', P, A, sub_from(P, G, gam2)), 'subdivision mismatch'
    # step 3: the layered composite V over P2
    ncol = len(tree2)
    srcs = [v(lab2[('f', (c,))]) for c in range(ncol)]
    tgts = []
    for c in range(ncol):
        kids = tree2[c]
        tgts.append(v(lab2[('y', (c, len(kids) - 1))]) if kids else v(lab2[('f', (c,))]))
    Ws = []
    for c in range(ncol):
        for j in range(len(tree2[c])):
            b = v(lab2[('f', (c, j))])
            Lt = rcomp(P2, tgts[:c]) if c > 0 else None
            Rt = rcomp(P2, srcs[c + 1:]) if c < ncol - 1 else None
            W = b
            if Lt is not None: W = comp2(P2, 0, Lt, W)
            if Rt is not None: W = comp2(P2, 0, W, Rt)
            Ws.append((W, Lt, b, Rt))
    V = lfold(P2, 1, [w[0] for w in Ws])
    k1 = kappa(P2, src(P2, cohz), src(P2, V))
    k2 = kappa(P2, tgt(P2, V), tgt(P2, cohz))
    Vh_parts = [k1] + [w[0] for w in Ws] + [k2]
    Vh = lfold(P2, 1, Vh_parts)
    TA = infer(P2, cohz)
    f2 = subst_tm(('coh', P2, arr(TA, cohz, Vh), tuple(v(i) for i in range(len(P2)))), g2)
    b2 = subst_tm(('coh', P2, arr(TA, Vh, cohz), tuple(v(i) for i in range(len(P2)))), g2)
    # step 4: expand each whiskered item
    parts = [subst_tm(k1, g2)] + [subst_tm(w[0], g2) for w in Ws] + [subst_tm(k2, g2)]
    new_items_groups = [[('S', parts[0])]]
    cf, cb = [None], [None]
    flat_items = []
    for (W, Lt, b, Rt), part in zip(Ws, parts[1:-1]):
        bimg = beta_img[b[1]]
        # which item was it?
        it = None
        for a in two:
            for itm in sub_nf[a].items:
                if item_term_x(G, itm) == bimg: it = itm
        if it[0] == 'S':
            new_items_groups.append([('S', part)]); cf.append(None); cb.append(None)
        elif it[0] == 'X':
            Lg = subst_tm(Lt, g2) if Lt is not None else None
            Rg = subst_tm(Rt, g2) if Rt is not None else None
            Wg, items, f, bk = abstract_whisker_var(G, Lg, it[1], Rg)
            assert Wg == part, 'whisker abstraction mismatch (variable)'
            new_items_groups.append(items); cf.append(f); cb.append(bk)
        else:
            Lg = subst_tm(Lt, g2) if Lt is not None else None
            Rg = subst_tm(Rt, g2) if Rt is not None else None
            Wg, items, f, bk = abstract_whisker(G, Lg, it[1], Rg)
            assert Wg == part, 'whisker abstraction mismatch'
            new_items_groups.append(items); cf.append(f); cb.append(bk)
    new_items_groups.append([('S', parts[-1])]); cf.append(None); cb.append(None)
    f3 = functor_column(G, parts, cf)
    expanded = [real_x(G, grp) for grp in new_items_groups]
    b3 = functor_column(G, expanded, cb)
    # reassociate nested folds into one flat fold
    flat = [it for grp in new_items_groups for it in grp]
    shape_src, off = [], 0
    for grp in new_items_groups:
        shape_src.append(flat_shape(len(grp), off)); off += len(grp)
    terms = [item_term_x(G, it) for it in flat]
    f4, b4 = reassoc(G, terms, shape_src, flat_shape(len(flat)))
    fwd = vc3(G, [f1, f2, f3, f4])
    bwd = vc3(G, [b4, b3, b2, b1])
    return NF(flat, fwd, bwd)



def item_term_x(G, it):
    if it[0] == 'X':
        return v(it[1])
    return item_term(G, it)

def real_x(G, items):
    return lfold(G, 1, [item_term_x(G, it) for it in items])

def abstract_whisker_var(G, L, x, R):
    """Lemma G(i) for a bare 2-variable: W = (L *0 x) *0 R (L, R optional
    1-terms). Returns W, the items [kappa, H_g, kappa] and the cells
    W => their composite and back, each one coherence over P_g."""
    pl = path(G, L)[0] if L is not None else ()
    pr = path(G, R)[0] if R is not None else ()
    g2 = (tuple(pl), x, tuple(pr))
    P, pre, zm, zp, Z, suf = Pg_info(len(g2[0]), len(g2[2]))
    th = rc2.theta(G, g2)
    ren = {}
    for i, t in enumerate(th):
        if t[0] == 'v' and tdim(G[t[1]]) <= 0 and i not in (zm, zp):
            ren[t[1]] = i
    Wt = v(Z)
    if L is not None: Wt = comp2(P, 0, rc2.rename(L, ren), Wt)
    if R is not None: Wt = comp2(P, 0, Wt, rc2.rename(R, ren))
    W = subst_tm(Wt, th)
    Hp = H_over(len(g2[0]), len(g2[2]))
    k1 = kappa(P, src(P, Wt), src(P, Hp))
    k2 = kappa(P, tgt(P, Hp), tgt(P, Wt))
    tgtP = lfold(P, 1, [k1, Hp, k2])
    A = infer(P, Wt)
    fwd = ('coh', P, arr(A, Wt, tgtP), th)
    bwd = ('coh', P, arr(A, tgtP, Wt), th)
    items = [('S', subst_tm(k1, th)), ('H', g2), ('S', subst_tm(k2, th))]
    assert real(G, items) == subst_tm(tgtP, th)
    return W, items, fwd, bwd


def normalize_top(G, T):
    """normalize_small, with a bare 2-variable at top level handled like rc2."""
    if T[0] == 'v':
        return normalize(G, T)
    return normalize_small(G, T)
