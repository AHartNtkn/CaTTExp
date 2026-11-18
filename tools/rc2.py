"""
Theorem A (RC(2)) as an algorithm, for contexts of dimension <= 2 with an
acyclic 1-skeleton: given parallel 2-terms T, T' whose normal forms have the
same sequence of whiskered generators, build a 3-term T => T'.

(The exchange step of Theorem A is not implemented: it is not needed when
the generator sequence is forced, as in the ladder of a chain.)

Every term built here is re-checked by catt.infer.
"""
from catt import *

# ---------------------------------------------------------------- labelled trees

def tree_labels(tree):
    """Emit ctx for tree and return dict: ('x',) -> 0, ('y', path) -> var, ('f', path) -> var."""
    lab = {('x',): 0}
    n = [1]
    def emit(node, prefix):
        for i, child in enumerate(node):
            p = prefix + (i,)
            lab[('y', p)] = n[0]; n[0] += 1
            lab[('f', p)] = n[0]; n[0] += 1
            emit(child, p)
    emit(tree, ())
    return lab

def ctx_dim2_vars(G):
    return {i for i, A in enumerate(G) if tdim(A) + 1 == 2}

def has2(G, t):
    return bool(fv_tm(t) & ctx_dim2_vars(G))

# ---------------------------------------------------------------- paths

def path(G, a):
    """Flattened edge word of a 1-term, with endpoints (s, t) as vertex vars."""
    A = infer(G, a)
    assert tdim(A) == 0
    s0, t0 = A[2][1], A[3][1]
    return tuple(_word(G, a)), s0, t0

def _word(G, a):
    if a[0] == 'v':
        return [a[1]]
    _, P, B, s = a
    # 1-term: arity of dim <= 1; collect words of the 1-dim arguments in order
    out = []
    for i, A in enumerate(P):
        if tdim(A) == 0:      # a 1-variable of the arity
            out += _word(G, s[i])
    return out

def chain_ren(G, w, s0):
    """Chain context C(w) and map Gamma-var -> C-var (acyclic: injective)."""
    C = tree_ctx(chain_tree(len(w)))
    ren = {s0: 0}
    for k, e in enumerate(w):
        ren[e] = 2 * k + 2
        ren[G[e][3][1]] = 2 * k + 1
    iota = [None] * len(C)
    for g, c in ren.items():
        iota[c] = v(g)
    return C, ren, tuple(iota)

def rename(t, ren):
    if t[0] == 'v':
        return v(ren[t[1]])
    return ('coh', t[1], t[2], tuple(rename(u, ren) for u in t[3]))

def struct_cell(G, a, b):
    """For parallel terms a, b without 2-variables (dim >= 1) lying over one
    path: the coherence a -> b over the chain context of that path."""
    A = infer(G, a)
    assert A == infer(G, b), 'struct_cell: not parallel'
    # find the path: the 1-dim source boundary of a
    one = a if tdim(A) == 0 else None
    B = A
    while tdim(B) > 0:
        B = B[1]
    # B is the type of the 1-dim boundary: s0 -> t0 ; take the 1-dim source term
    T = A
    t1 = a
    while tdim(T) > 0:
        t1 = T[2]; T = T[1]
    w, s0, t0 = path(G, t1)
    C, ren, iota = chain_ren(G, w, s0)
    at, bt = rename(a, ren), rename(b, ren)
    TA = infer(C, at)
    term = ('coh', C, arr(TA, at, bt), iota)
    assert infer(G, term) == arr(A, a, b)
    return term

def kappa(G, a, b):
    return struct_cell(G, a, b)

def ident(G, x):
    """identity on a vertex var x"""
    D0 = tree_ctx(())
    return ('coh', D0, arr(STAR, v(0), v(0)), (v(x),))

def rcomp(G, terms, vert=None):
    if not terms:
        return ident(G, vert)
    t = terms[-1]
    for u in reversed(terms[:-1]):
        t = comp2(G, 0, u, t)
    return t

def lfold(G, k, terms):
    t = terms[0]
    for u in terms[1:]:
        t = comp2(G, k, t, u)
    return t

def vc3(G, cells):
    cells = [c for c in cells if c is not None]
    if not cells: return None
    return lfold(G, 2, cells)

# ---------------------------------------------------------------- whiskered generators

def Pg_tree(nl, nr):
    return tuple([()] * nl + [((),)] + [()] * nr)

def Pg_info(nl, nr):
    tree = Pg_tree(nl, nr)
    P = tree_ctx(tree)
    lab = tree_labels(tree)
    pre = [lab[('f', (i,))] for i in range(nl)]
    zm = lab[('f', (nl,))]
    zp = lab[('y', (nl, 0))]
    Z = lab[('f', (nl, 0))]
    suf = [lab[('f', (nl + 1 + i,))] for i in range(nr)]
    return P, pre, zm, zp, Z, suf

def N_over(P, pre, z, suf):
    return rcomp(P, [v(e) for e in pre] + [v(z)] + [v(e) for e in suf])

def H_over(nl, nr):
    P, pre, zm, zp, Z, suf = Pg_info(nl, nr)
    a = N_over(P, pre, zm, suf); b = N_over(P, pre, zp, suf)
    return ('coh', P, arr(infer(P, a), a, b), tuple(v(i) for i in range(len(P))))

def theta(G, g):
    lam, x, rho = g
    P, pre, zm, zp, Z, suf = Pg_info(len(lam), len(rho))
    images = {Z: v(x)}
    for e, ge in zip(pre, lam): images[e] = v(ge)
    for e, ge in zip(suf, rho): images[e] = v(ge)
    return sub_from(P, G, images)

def H_term(G, g):
    return subst_tm(H_over(len(g[0]), len(g[2])), theta(G, g))

def N_term(G, g, sign):
    lam, x, rho = g
    P, pre, zm, zp, Z, suf = Pg_info(len(lam), len(rho))
    return subst_tm(N_over(P, pre, zm if sign == '-' else zp, suf), theta(G, g))

# ---------------------------------------------------------------- vertical chains and reassociation

def vchain_tree(m):
    return ((tuple(() for _ in range(m)),),)  # unused

def column(m):
    """ps: one 1-cell slot with m vertical 2-cells; returns (tree, beta vars)."""
    tree = (tuple(() for _ in range(m)),)
    lab = tree_labels(tree)
    betas = [lab[('f', (0, j))] for j in range(m)]
    return tree, betas

def bracket_term(P, shape, betas):
    """shape: nested lists of ints (indices into betas); left fold at each level."""
    if isinstance(shape, int):
        return v(betas[shape])
    parts = [bracket_term(P, s, betas) for s in shape]
    return lfold(P, 1, parts)

def reassoc(G, items, shape_src, shape_tgt):
    """3-cell between two bracketings of the vertical composite of 2-terms."""
    tree, betas = column(len(items))
    P = tree_ctx(tree)
    a = bracket_term(P, shape_src, betas)
    b = bracket_term(P, shape_tgt, betas)
    if a == b:
        return None, None
    s = sub_from(P, G, dict(zip(betas, items)))
    A = infer(P, a)
    f = ('coh', P, arr(A, a, b), s)
    r = ('coh', P, arr(A, b, a), s)
    return f, r

def flat_shape(n, off=0):
    return list(range(off, off + n)) if n > 1 else off

def functor_column(G, items, cells):
    """items: list of 2-terms (vertical composable); cells: list of (fwd) 3-cells or None,
    cell_i : items[i] => items'[i]. Returns 3-cell lfold(items) => lfold(items')."""
    m = len(items)
    tree0, betas0 = column(m)
    P0 = tree_ctx(tree0)
    body = bracket_term(P0, flat_shape(m), betas0) if m > 1 else v(betas0[0])
    return functor(G, ('coh', P0, None, None), P0, tree0, body,
                   {betas0[i]: items[i] for i in range(m)},
                   {betas0[i]: cells[i] for i in range(m) if cells[i] is not None})

def functor(G, _unused, P, tree, body, base_images, cells):
    """body: a 2-term over ps P (= tree_ctx(tree)). base_images: images of all 2-vars and
    of maximal 1-vars. cells: 2-var -> 3-cell (in G) from its image to a new term.
    Returns 3-cell body[base] => body[new]."""
    if not cells:
        return None
    lab = tree_labels(tree)
    inv = {vv: k for k, vv in lab.items()}
    # build P3: replace leaf at the path of each changed 2-var by ((),)
    changed_paths = {inv[a][1] for a in cells}
    def rebuild(node, prefix):
        out = []
        for i, child in enumerate(node):
            p = prefix + (i,)
            if p in changed_paths:
                assert child == ()
                out.append(((),))
            else:
                out.append(rebuild(child, p))
        return tuple(out)
    tree3 = rebuild(tree, ())
    P3 = tree_ctx(tree3)
    lab3 = tree_labels(tree3)
    def incl(sign):
        s = []
        for i in range(len(P)):
            k = inv[i]
            if k[0] == 'f' and k[1] in changed_paths and sign == '+':
                s.append(v(lab3[('y', k[1] + (0,))]))
            else:
                s.append(v(lab3[k]))
        return tuple(s)
    src3 = subst_tm(body, incl('-'))
    tgt3 = subst_tm(body, incl('+'))
    A = infer(P3, src3)
    images = {}
    for pv, t in base_images.items():
        k = inv[pv]
        if pv in cells:
            images[lab3[('f', k[1] + (0,))]] = cells[pv]
        else:
            images[lab3[k]] = t
    s = sub_from(P3, G, images)
    term = ('coh', P3, arr(A, src3, tgt3), s)
    infer(G, term)
    return term

# ---------------------------------------------------------------- normalization

class NF:
    def __init__(self, items, fwd, bwd):
        self.items, self.fwd, self.bwd = items, fwd, bwd

def item_term(G, it):
    return it[1] if it[0] == 'S' else H_term(G, it[1])

def real(G, items):
    return lfold(G, 1, [item_term(G, it) for it in items])

def abstract_whisker(G, L, x_g, R):
    """W = (L *0 H_g[theta]) *0 R (L, R optional 1-terms). Returns items and cells
    W => kappa1 * H_g' * kappa2 and back."""
    lam, x, rho = x_g
    pl = path(G, L)[0] if L is not None else ()
    pr = path(G, R)[0] if R is not None else ()
    g2 = (tuple(pl) + tuple(lam), x, tuple(rho) + tuple(pr))
    P, pre, zm, zp, Z, suf = Pg_info(len(g2[0]), len(g2[2]))
    # renaming Gamma -> P for the 1-dim data
    th = theta(G, g2)
    ren = {}
    for i, t in enumerate(th):
        if t[0] == 'v' and tdim(G[t[1]]) <= 0 and i not in (zm, zp):
            ren[t[1]] = i
    # inner H_g over P: send P_g maximal vars to P vars
    Pi, prei, zmi, zpi, Zi, sufi = Pg_info(len(lam), len(rho))
    im = {Zi: v(Z)}
    for k, e in enumerate(prei): im[e] = v(pre[len(pl) + k])
    for k, e in enumerate(sufi): im[e] = v(suf[k])
    Hin = subst_tm(H_over(len(lam), len(rho)), sub_from(Pi, P, im))
    Wt = Hin
    if L is not None: Wt = comp2(P, 0, rename(L, ren), Wt)
    if R is not None: Wt = comp2(P, 0, Wt, rename(R, ren))
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

def normalize(G, T):
    """Returns NF with fwd: T => real(items), bwd: real(items) => T."""
    if not has2(G, T):
        return NF([('S', T)], None, None)
    if T[0] == 'v':
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
    sub_nf = {a: normalize(G, gam[a]) for a in two}
    # step 1: functoriality T => coh_P[gam']
    base = {i: gam[i] for i in maximal_vars(P)}
    body = ('coh', P, A, tuple(v(i) for i in range(len(P))))
    f1 = functor(G, None, P, tree, body, base, {a: n.fwd for a, n in sub_nf.items() if n.fwd is not None})
    gam2 = dict(base);
    for a, n in sub_nf.items(): gam2[a] = real(G, n.items)
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
                    beta_img[b] = item_term(G, it)
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
                if item_term(G, itm) == bimg: it = itm
        if it[0] == 'S':
            new_items_groups.append([('S', part)]); cf.append(None); cb.append(None)
        else:
            Lg = subst_tm(Lt, g2) if Lt is not None else None
            Rg = subst_tm(Rt, g2) if Rt is not None else None
            Wg, items, f, bk = abstract_whisker(G, Lg, it[1], Rg)
            assert Wg == part, 'whisker abstraction mismatch'
            new_items_groups.append(items); cf.append(f); cb.append(bk)
    new_items_groups.append([('S', parts[-1])]); cf.append(None); cb.append(None)
    f3 = functor_column(G, parts, cf)
    expanded = [real(G, grp) for grp in new_items_groups]
    b3 = functor_column(G, expanded, cb)
    # reassociate nested folds into one flat fold
    flat = [it for grp in new_items_groups for it in grp]
    shape_src, off = [], 0
    for grp in new_items_groups:
        shape_src.append(flat_shape(len(grp), off)); off += len(grp)
    terms = [item_term(G, it) for it in flat]
    f4, b4 = reassoc(G, terms, shape_src, flat_shape(len(flat)))
    fwd = vc3(G, [f1, f2, f3, f4])
    bwd = vc3(G, [b4, b3, b2, b1])
    return NF(flat, fwd, bwd)

def canon(G, nf, A, B):
    """Group S-runs and replace each by the canonical kappa. Returns (gens, canon_term, fwd, bwd)."""
    items = nf.items
    groups, cur = [], []
    gens = []
    for it in items:
        if it[0] == 'S':
            cur.append(it)
        else:
            groups.append(cur); cur = []
            groups.append([it]); gens.append(it[1])
    groups.append(cur)
    assert all(groups[i] for i in range(0, len(groups), 2)), 'empty S-run'
    terms = [item_term(G, it) for it in items]
    shape, off = [], 0
    for grp in groups:
        shape.append(flat_shape(len(grp), off)); off += len(grp)
    f1, b1 = reassoc(G, terms, flat_shape(len(terms)), shape)
    gterms = [lfold(G, 1, [item_term(G, it) for it in grp]) for grp in groups]
    canon_terms, cf, cb = [], [], []
    for i, (grp, gt) in enumerate(zip(groups, gterms)):
        if grp[0][0] == 'H':
            canon_terms.append(gt); cf.append(None); cb.append(None)
        else:
            a, b = src(G, gt), tgt(G, gt)
            k = kappa(G, a, b)
            canon_terms.append(k)
            if k == gt:
                cf.append(None); cb.append(None)
            else:
                cf.append(struct_cell(G, gt, k)); cb.append(struct_cell(G, k, gt))
    f2 = functor_column(G, gterms, cf)
    b2 = functor_column(G, canon_terms, cb)
    return gens, lfold(G, 1, canon_terms), vc3(G, [nf.fwd, f1, f2]), vc3(G, [b2, b1, nf.bwd])

def rc2(G, T, U):
    nT, nU = normalize(G, T), normalize(G, U)
    gT, cT, fT, bT = canon(G, nT, src(G, T), tgt(G, T))
    gU, cU, fU, bU = canon(G, nU, src(G, U), tgt(G, U))
    assert gT == gU, ('generator sequences differ (exchange not implemented)', gT, gU)
    assert cT == cU
    K = vc3(G, [fT, bU])
    assert infer(G, K) == arr(infer(G, T), T, U)
    return K

# ---------------------------------------------------------------- exchange (Lemma E)

def E_info(nl, nm, nr):
    tree = tuple([()] * nl + [((),)] + [()] * nm + [((),)] + [()] * nr)
    P = tree_ctx(tree); lab = tree_labels(tree)
    pre = [lab[('f', (i,))] for i in range(nl)]
    z1m, z1p, Z1 = lab[('f', (nl,))], lab[('y', (nl, 0))], lab[('f', (nl, 0))]
    mid = [lab[('f', (nl + 1 + i,))] for i in range(nm)]
    o = nl + 1 + nm
    z2m, z2p, Z2 = lab[('f', (o,))], lab[('y', (o, 0))], lab[('f', (o, 0))]
    suf = [lab[('f', (o + 1 + i,))] for i in range(nr)]
    return P, pre, (z1m, z1p, Z1), mid, (z2m, z2p, Z2), suf

def column_into(P, nl, nr, pre_imgs, Z, suf_imgs):
    Pc, pre, zm, zp, Zc, suf = Pg_info(nl, nr)
    im = {Zc: v(Z)}
    for e, t in zip(pre, pre_imgs): im[e] = t
    for e, t in zip(suf, suf_imgs): im[e] = t
    return subst_tm(H_over(nl, nr), sub_from(Pc, P, im))

def swap_split(G, g1, g2):
    lam, x, r1 = g1
    l2, y, rho = g2
    tx = path(G, tgt(G, v(x)))[0]
    sy = path(G, src(G, v(y)))[0]
    assert l2[:len(lam)] == lam and l2[len(lam):len(lam) + len(tx)] == tx, 'not side by side'
    mu = l2[len(lam) + len(tx):]
    assert r1 == mu + sy + rho, 'not side by side'
    return lam, mu, rho

def exchange_cell(G, g1, g2, a_prev, b_next):
    """Z => Z', where Z, Z' have canonical forms [k, H_g1, k, H_g2, k] and the swapped one,
    from a_prev to b_next. Returns (Z, Z', cell, cellrev, g2', g1')."""
    lam, mu, rho = swap_split(G, g1, g2)
    x, y = g1[1], g2[1]
    P, pre, (z1m, z1p, Z1), mid, (z2m, z2p, Z2), suf = E_info(len(lam), len(mu), len(rho))
    V_ = lambda ls: [v(e) for e in ls]
    H1 = column_into(P, len(pre), len(mid) + 1 + len(suf), V_(pre), Z1, V_(mid) + [v(z2m)] + V_(suf))
    H2 = column_into(P, len(pre) + 1 + len(mid), len(suf), V_(pre) + [v(z1p)] + V_(mid), Z2, V_(suf))
    H2b = column_into(P, len(pre) + 1 + len(mid), len(suf), V_(pre) + [v(z1m)] + V_(mid), Z2, V_(suf))
    H1b = column_into(P, len(pre), len(mid) + 1 + len(suf), V_(pre), Z1, V_(mid) + [v(z2p)] + V_(suf))
    Sc = rcomp(P, V_(pre) + [v(z1m)] + V_(mid) + [v(z2m)] + V_(suf))
    Tc = rcomp(P, V_(pre) + [v(z1p)] + V_(mid) + [v(z2p)] + V_(suf))
    TE = lfold(P, 1, [kappa(P, Sc, src(P, H1)), H1, kappa(P, tgt(P, H1), src(P, H2)), H2, kappa(P, tgt(P, H2), Tc)])
    TEb = lfold(P, 1, [kappa(P, Sc, src(P, H2b)), H2b, kappa(P, tgt(P, H2b), src(P, H1b)), H1b, kappa(P, tgt(P, H1b), Tc)])
    A = infer(P, TE)
    im = {Z1: v(x), Z2: v(y)}
    for e, ge in zip(pre, lam): im[e] = v(ge)
    for e, ge in zip(mid, mu): im[e] = v(ge)
    for e, ge in zip(suf, rho): im[e] = v(ge)
    th = sub_from(P, G, im)
    t1, t2 = subst_tm(TE, th), subst_tm(TEb, th)
    e_f = ('coh', P, arr(A, TE, TEb), th)
    e_b = ('coh', P, arr(A, TEb, TE), th)
    ka, kb = kappa(G, a_prev, src(G, t1)), kappa(G, tgt(G, t1), b_next)
    def wrap(cell):
        return comp2(G, 1, comp2(G, 1, ka, cell), kb)
    Z1t = lfold(G, 1, [ka, t1, kb]); Z2t = lfold(G, 1, [ka, t2, kb])
    return Z1t, Z2t, wrap(e_f), wrap(e_b)

def canon_term(G, gens, A, B):
    items = []
    prev = A
    for g in gens:
        items.append(kappa(G, prev, N_term(G, g, '-')))
        items.append(H_term(G, g)); prev = N_term(G, g, '+')
    items.append(kappa(G, prev, B))
    return items

def swap_in_canon(G, gens, i, A, B):
    """3-cells between canonical forms differing by swapping gens[i], gens[i+1]."""
    items = canon_term(G, gens, A, B)
    g1, g2 = gens[i], gens[i + 1]
    a_prev = A if i == 0 else N_term(G, gens[i - 1], '+')
    b_next = B if i + 2 == len(gens) else N_term(G, gens[i + 2], '-')
    Zt, Zt2, ef, eb = exchange_cell(G, g1, g2, a_prev, b_next)
    nZ, nZ2 = normalize(G, Zt), normalize(G, Zt2)
    gz, cz, fz, bz = canon(G, nZ, a_prev, b_next)
    gz2, cz2, fz2, bz2 = canon(G, nZ2, a_prev, b_next)
    assert gz == [g1, g2], (gz, [g1, g2])
    new = list(gens); new[i], new[i + 1] = gz2[0], gz2[1]
    window_f = vc3(G, [bz, ef, fz2])       # canon(window) => canon(window')
    window_b = vc3(G, [bz2, eb, fz])
    items2 = canon_term(G, new, A, B)
    # window = items[2i : 2i+5]
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

def rc2_full(G, T, U):
    nT, nU = normalize(G, T), normalize(G, U)
    A, B = src(G, T), tgt(G, T)
    gT, cT, fT, bT = canon(G, nT, A, B)
    gU, cU, fU, bU = canon(G, nU, A, B)
    fwd, cur = [fT], list(gT)
    target = [g[1] for g in gU]
    for pos, x in enumerate(target):
        j = next(k for k in range(pos, len(cur)) if cur[k][1] == x)
        while j > pos:
            cur, f, b = swap_in_canon(G, cur, j - 1, A, B)
            fwd.append(f); j -= 1
    assert cur == gU, (cur, gU)
    fwd.append(bU)
    K = vc3(G, fwd)
    assert infer(G, K) == arr(infer(G, T), T, U)
    return K
