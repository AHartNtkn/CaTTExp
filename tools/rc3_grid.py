"""
Checks toward RC(3) on the 2 x 2 grid (the Gray product of two paths of
length 2), notes/relative-coherence.md §7.8.

    vertices (i, j), 0 <= i, j <= 2
    h_ij : (i,j) -> (i+1,j)        v_ij : (i,j) -> (i,j+1)
    S_ij : h_ij *0 v_{i+1,j}  =>  v_ij *0 h_{i,j+1}        (i, j < 2)

The six paths (0,0) -> (2,2) form the lattice
    bot = hhvv < a = hvhv < b = vhhv, b' = hvvh < c = vhvh < top = vvhh,
i.e. L = {bot} + {0,1}^2 + {top}: the four middle paths are exactly the
paths through (1,1), written l_i r_j.  All exchange happens inside the
block {0,1}^2, where (1,1) is a cut vertex of every cell.

We check:
  * the strict-cell classification (exchange classes of 2-paths = intervals
    of L, by brute-force enumeration of whiskered-generator words);
  * the head-shape lemma on generated terms: the 0-vertices of an arity go
    to common vertices of the two boundary paths; a term whose value is a
    prime interval (no common inner vertex) has exactly one active column;
    two active columns are always split at (1,1);
  * literal frame factorisations gamma = delta[eta] (H typed over R);
  * the normal forms N_{p,q} (chain letters E_up, E_dn and block letters
    a *0 b with identity factors retained) for every interval of L;
  * the multiplication mu_{p,q,r} : N_{p,q} . N_{q,r} => N_{p,r} for every
    composable pair: reassociation, junction contraction, and at a
    block/block junction kappa(q,q) => 1, unit removal and the block merge
    M = I ; (m^F *0 m^G);
  * the exchange chi at a -> c and its compatibility 4-term (8), the raw
    associativity law (12) in the block, Z_3 and zeta;
  * the core interchange 4-cell of the mixed mu-law (a block merge and a
    separator contraction at disjoint positions).
Everything is re-checked by catt.infer here and by the certified Agda
checker in src/CaTTExp/Generated/GridRC3.agda.
"""
import random, itertools
from catt import *
from rc2 import struct_cell, ident, path, lfold
from rc3_wedge import factor_cols, eta_witness, two
from rc3_square import column_ranges

# ---------------------------------------------------------------- generic helpers
D1 = tree_ctx(((),))            # x, y, f
D2 = tree_ctx((((),),))         # x, y, f, g, z : f => g

def id2(G, t):
    """Identity 2-cell on a 1-term t."""
    A = arr(arr(STAR, v(0), v(1)), v(2), v(2))
    return ('coh', D1, A, sub_from(D1, G, {2: t}))

def CN(n):
    return tree_ctx(((tuple(() for _ in range(n))),))

def zvar(i):
    return v(2 + 2 * i)

def full_coh(P, s, t, sig):
    A = infer(P, s)
    assert A == infer(P, t), 'full_coh: not parallel'
    return subst_tm(('coh', P, arr(A, s, t), tuple(v(i) for i in range(len(P)))), sig)

def reassoc_list(G, L, groups_src, groups_tgt):
    """Over C_N: a coherence between two bracketings of the vertical list L.
    groups_* are nested tuples of indices describing the bracketing."""
    n = len(L)
    P = CN(n)
    zs = [zvar(i) for i in range(1, n + 1)]
    def build(gr):
        if isinstance(gr, int):
            return zs[gr]
        return lfold(P, 1, [build(x) for x in gr])
    sig = sub_from(P, G, {2 + 2 * i: L[i - 1] for i in range(1, n + 1)})
    return full_coh(P, build(groups_src), build(groups_tgt), sig)

def lf_groups(n):
    return tuple(range(n))

def insert3(G, L, i, j, cell):
    """L a vertical list of 2-terms; cell a 3-term with source the left fold of
    L[i:j].  Returns (term, L') with term : lfold(L) => lfold(L'), where
    L' = L[:i] + [target of cell] + L[j:]."""
    n = len(L)
    src_tgt = infer(G, cell)
    X = src_tgt[3]
    assert src_tgt[2] == lfold(G, 1, L[i:j]), 'insert3: cell source mismatch'
    if j - i == 1 and n == 1:
        return cell, [X]
    # step 1: group L[i:j] into one slot
    grouped = tuple(range(i)) + ((tuple(range(i, j)),) if j - i > 1 else (i,)) + tuple(range(j, n))
    steps = []
    if j - i > 1:
        steps.append(reassoc_list(G, L, lf_groups(n), grouped))
    Lg = L[:i] + [lfold(G, 1, L[i:j])] + L[j:]
    m = len(Lg)
    # step 2: insert the 3-cell at slot i of V_m(0..1..0)
    slots = [() for _ in range(m)]
    slots[i] = ((),)
    V = tree_ctx((tuple(slots),))
    threes = [k for k, A in enumerate(V) if tdim(A) == 2]
    h = threes[0]
    z0, z1 = V[h][2], V[h][3]
    twos = [k for k, A in enumerate(V) if tdim(A) == 1 and v(k) not in (z0, z1)]
    others = [v(k) for k in twos]
    vs = lfold(V, 1, others[:i] + [z0] + others[i:]) if m > 1 else z0
    vt = lfold(V, 1, others[:i] + [z1] + others[i:]) if m > 1 else z1
    imgs = {h: cell}
    for var, t in zip(twos, Lg[:i] + Lg[i + 1:]):
        imgs[var] = t
    sigV = sub_from(V, G, imgs)
    steps.append(full_coh(V, vs, vt, sigV))
    res = steps[0]
    for s_ in steps[1:]:
        res = comp2(G, 2, res, s_)
    Lnew = L[:i] + [X] + L[j:]
    assert infer(G, res)[3] == lfold(G, 1, Lnew)
    return res, Lnew

def vcomp3(G, cells):
    return lfold(G, 2, cells)

def unit_cell(G, x, y):
    """x . y => the non-identity one, where one of x, y is an identity 2-cell."""
    if x == id2(G, infer(G, x)[2]) and x != y:
        s = comp2(D2, 1, id2(D2, v(2)), v(4)); tz = y
    else:
        s = comp2(D2, 1, v(4), id2(D2, v(3))); tz = x
    return full_coh(D2, s, v(4), sub_from(D2, G, {4: tz}))

P22 = tree_ctx((((), ()), ((), ())))  # x, y1, u0, u1, z1, u2, z2, y2, w0, w1, q1, w2, q2

def interchange_I(G, a, b, a_, b_):
    """I : (a *0 b) . (a_ *0 b_) => (a . a_) *0 (b . b_)  over C_2 *0 C_2."""
    z1, z2, q1, q2 = v(4), v(6), v(10), v(12)
    s = comp2(P22, 1, comp2(P22, 0, z1, q1), comp2(P22, 0, z2, q2))
    t = comp2(P22, 0, comp2(P22, 1, z1, z2), comp2(P22, 1, q1, q2))
    return full_coh(P22, s, t, sub_from(P22, G, {4: a, 6: a_, 10: b, 12: b_}))

def rnest(G, ts):
    t = ts[-1]
    for u in reversed(ts[:-1]):
        t = comp2(G, 0, u, t)
    return t

# ---------------------------------------------------------------- the grid
def build():
    G = []
    V = {}
    for i in range(3):
        for j in range(3):
            V[i, j] = len(G); G.append(STAR)
    H, Vv = {}, {}
    for i in range(3):
        for j in range(3):
            if i < 2:
                H[i, j] = len(G); G.append(arr(STAR, v(V[i, j]), v(V[i + 1, j])))
            if j < 2:
                Vv[i, j] = len(G); G.append(arr(STAR, v(V[i, j]), v(V[i, j + 1])))
    S = {}
    for i in range(2):
        for j in range(2):
            Gt = tuple(G)
            s = comp2(Gt, 0, v(H[i, j]), v(Vv[i + 1, j]))
            t = comp2(Gt, 0, v(Vv[i, j]), v(H[i, j + 1]))
            S[i, j] = len(G)
            G.append(arr(arr(STAR, v(V[i, j]), v(V[i + 1, j + 1])), s, t))
    G = tuple(G)
    check_ctx(G)
    return G, V, H, Vv, S

G, VX, HX, VY, SQ = build()
VERT = {VX[k]: k for k in VX}
h = lambda i, j: v(HX[i, j])
vv = lambda i, j: v(VY[i, j])
sq = lambda i, j: v(SQ[i, j])
def c0(a, b): return comp2(G, 0, a, b)
def c1(a, b): return comp2(G, 1, a, b)
def kap(a, b): return struct_cell(G, a, b)

# paths (0,0) -> (2,2) as edge lists
PATHS = {
    'bot': [h(0, 0), h(1, 0), vv(2, 0), vv(2, 1)],
    (0, 0): [h(0, 0), vv(1, 0), h(1, 1), vv(2, 1)],     # a  = l0 r0
    (1, 0): [vv(0, 0), h(0, 1), h(1, 1), vv(2, 1)],     # b  = l1 r0
    (0, 1): [h(0, 0), vv(1, 0), vv(1, 1), h(1, 2)],     # b' = l0 r1
    (1, 1): [vv(0, 0), h(0, 1), vv(1, 1), h(1, 2)],     # c  = l1 r1
    'top': [vv(0, 0), vv(0, 1), h(0, 2), h(1, 2)],
}
ELEMS = ['bot', (0, 0), (1, 0), (0, 1), (1, 1), 'top']
LV = {0: c0(h(0, 0), vv(1, 0)), 1: c0(vv(0, 0), h(0, 1))}       # l0, l1
RV = {0: c0(h(1, 1), vv(2, 1)), 1: c0(vv(1, 1), h(1, 2))}       # r0, r1

def rep(p):
    if p in ('bot', 'top'):
        return rnest(G, PATHS[p])
    return c0(LV[p[0]], RV[p[1]])

def leq(p, q):
    if p == q or p == 'bot' or q == 'top':
        return True
    if p == 'top' or q == 'bot':
        return False
    return p[0] <= q[0] and p[1] <= q[1]

E_UP = c0(h(0, 0), c0(sq(1, 0), vv(2, 1)))
E_DN = c0(vv(0, 0), c0(sq(0, 1), h(1, 2)))
assert infer(G, E_UP)[3] == c0(h(0, 0), c0(c0(vv(1, 0), h(1, 1)), vv(2, 1)))

def E_blk(p, q):
    a = sq(0, 0) if (p[0], q[0]) == (0, 1) else id2(G, LV[p[0]])
    b = sq(1, 1) if (p[1], q[1]) == (0, 1) else id2(G, RV[p[1]])
    return c0(a, b)

def word(p, q):
    assert leq(p, q)
    if p == q:
        return []
    out = []
    p_ = (0, 0) if p == 'bot' else p
    q_ = (1, 1) if q == 'top' else q
    if p == 'bot':
        out.append('up')
    if p_ != q_:
        out.append(('blk', p_, q_))
    if q == 'top':
        out.append('dn')
    return out

def letter_tm(x):
    if x == 'up': return E_UP
    if x == 'dn': return E_DN
    return E_blk(x[1], x[2])

def N_list(p, q, A, B):
    w = word(p, q)
    if not w:
        return [kap(A, B)]
    ls = [letter_tm(x) for x in w]
    out = [kap(A, infer(G, ls[0])[2])]
    for k, e in enumerate(ls):
        out.append(e)
        nxt = infer(G, ls[k + 1])[2] if k + 1 < len(ls) else B
        out.append(kap(infer(G, e)[3], nxt))
    return out

def N(p, q, A, B):
    return lfold(G, 1, N_list(p, q, A, B))

def lnest_path(p):
    return lfold(G, 0, PATHS[p])

# ---------------------------------------------------------------- the block merge
def merge_core(Ed, Ee, q):
    """(E_d . 1_q) . E_e => E_{de}: unit coherence on C_2, then I ; (m^F *0 m^G)."""
    one = id2(G, rep(q))
    P = CN(2)
    s = comp2(P, 1, comp2(P, 1, zvar(1), id2(P, v(3))), zvar(2))
    t = comp2(P, 1, zvar(1), zvar(2))
    u = full_coh(P, s, t, sub_from(P, G, {4: Ed, 6: Ee}))
    assert infer(G, u)[2] == c1(c1(Ed, one), Ee)
    a, b = horiz_factors(Ed)
    a_, b_ = horiz_factors(Ee)
    I = interchange_I(G, a, b, a_, b_)
    mF = unit_cell(G, a, a_)
    mG = unit_cell(G, b, b_)
    res = vcomp3(G, [u, I, comp2(G, 0, mF, mG)])
    return res

def horiz_factors(E):
    """For E = comp2(G, 0, a, b) with a, b 2-terms, return (a, b)."""
    _, P, A, s = E
    mx = maximal_vars(P)
    assert len(mx) == 2
    return s[mx[0]], s[mx[1]]

# ---------------------------------------------------------------- mu
def mu(p, q, r, A, B, Cc):
    Lu, Lv = N_list(p, q, A, B), N_list(q, r, B, Cc)
    m = len(Lu)
    L = Lu + Lv
    lhs = c1(lfold(G, 1, Lu), lfold(G, 1, Lv))
    cells = [reassoc_list(G, L, (tuple(range(m)), tuple(range(m, len(L)))), lf_groups(len(L)))]
    # contract the junction pair
    X_ = infer(G, L[m - 1])[2]; Z_ = infer(G, L[m])[3]
    mp = struct_cell(G, c1(L[m - 1], L[m]), kap(X_, Z_))
    t, L = insert3(G, L, m - 1, m + 1, mp)
    cells.append(t)
    wu, wv = word(p, q), word(q, r)
    if wu and wv and isinstance(wu[-1], tuple) and isinstance(wv[0], tuple):
        j = m - 1                                  # position of kappa(q^, q^)
        assert L[j] == kap(rep(q), rep(q))
        t, L = insert3(G, L, j, j + 1, struct_cell(G, L[j], id2(G, rep(q))))
        cells.append(t)
        core = merge_core(L[j - 1], L[j + 1], q)
        t, L = insert3(G, L, j - 1, j + 2, core)
        cells.append(t)
    res = vcomp3(G, cells)
    want_t = N(p, r, A, Cc)
    ty = infer(G, res)
    assert ty[2] == lhs and ty[3] == want_t, 'mu has the wrong type'
    return res, arr(ty[1], lhs, want_t)

# ---------------------------------------------------------------- strict classification
GENS = [((0, 0), 'S00'), ((1, 0), 'S10'), ((0, 1), 'S01'), ((1, 1), 'S11')]

def edge_name(t):
    k = t[1]
    for (i, j), x in HX.items():
        if x == k: return ('h', i, j)
    for (i, j), x in VY.items():
        if x == k: return ('v', i, j)

def apply_gen(pth, ij):
    """Apply square ij to an edge-name path if possible (unique position)."""
    i, j = ij
    src = [('h', i, j), ('v', i + 1, j)]
    tgt = [('v', i, j), ('h', i, j + 1)]
    for k in range(len(pth) - 1):
        if pth[k:k + 2] == src:
            return pth[:k] + tgt + pth[k + 2:], k
    return None

def classify():
    """Enumerate 2-paths (words of whiskered squares) from every path of L and
    their exchange classes; check: one class per interval of L."""
    names = {p: [edge_name(e) for e in PATHS[p]] for p in ELEMS}
    back = {tuple(v_): p for p, v_ in names.items()}
    words = {}       # (p, q) -> set of words (tuples of (square, position))
    def dfs(p0, cur, w):
        words.setdefault((p0, back[tuple(cur)]), set()).add(tuple(w))
        for (ij, _) in GENS:
            r = apply_gen(cur, ij)
            if r:
                dfs(p0, r[0], w + [(ij, r[1])])
    for p in ELEMS:
        dfs(p, names[p], [])
    # exchange: adjacent letters at disjoint positions swap
    def neighbours(w):
        for k in range(len(w) - 1):
            (g1, k1), (g2, k2) = w[k], w[k + 1]
            if k1 + 2 <= k2 or k2 + 2 <= k1:
                yield w[:k] + (w[k + 1], w[k]) + w[k + 2:]
    ncls = 0
    for (p, q), ws in words.items():
        ws = set(ws)
        seen = set(); classes = 0
        for w in ws:
            if w in seen: continue
            classes += 1
            stack = [w]; seen.add(w)
            while stack:
                x = stack.pop()
                for y in neighbours(x):
                    if y in ws and y not in seen:
                        seen.add(y); stack.append(y)
        assert classes == 1, ('several exchange classes', p, q)
        assert leq(p, q)
        ncls += 1
    assert ncls == sum(1 for p in ELEMS for q in ELEMS if leq(p, q))
    return ncls

# ---------------------------------------------------------------- values and head shapes
def value_of(t):
    A = infer(G, t)
    sw, a, b = path(G, A[2])
    tw, _, _ = path(G, A[3])
    return [VERT_OF_EDGE_SRC(e) for e in sw] + [b], [VERT_OF_EDGE_SRC(e) for e in tw] + [b], sw, tw

def VERT_OF_EDGE_SRC(e):
    return G[e][2][1]

def path_elem(w):
    for p in ELEMS:
        if [x[1] for x in PATHS[p]] == list(w):
            return p
    return None

def head_report(t):
    """t = coh_{P,A}[g] a 2- or 3-term with 0-boundary (0,0) -> (2,2).
    Checks the head-shape lemma; returns a label."""
    _, P, _A, g = t
    B = infer(G, t)
    while tdim(B) > 1:
        B = B[1]
    # B : 2-type  s => t' between 1-terms; boundary paths of the 1-dim faces
    s1, t1 = B[2], B[3]
    sw, a, b = path(G, s1); tw, _, _ = path(G, t1)
    sv = [VERT_OF_EDGE_SRC(e) for e in sw] + [b]
    tv = [VERT_OF_EDGE_SRC(e) for e in tw] + [b]
    common = set(sv) & set(tv)
    cols = column_ranges(tree_of(P))
    verts = [g[0][1]] + [g[s1_][1] for (_, s1_, _, _) in cols]
    assert all(x in common for x in verts), 'arity vertex not on both boundary paths'
    act = [jj for jj, (s0, s1_, f, e) in enumerate(cols) if any(two(G, g[i]) for i in range(f, e))]
    p, q = path_elem(sw), path_elem(tw)
    prime = (common == {VX[0, 0], VX[2, 2]})
    if prime and p != q:
        assert len(act) == 1, 'prime value with %d active columns' % len(act)
        return 'prime-1col'
    assert len(act) <= 2
    if len(act) == 2:
        j1, j2 = act
        assert g[cols[j1][1]] == v(VX[1, 1]) and g[cols[j2][0]] == v(VX[1, 1]), 'two active columns not split at (1,1)'
        return 'split(1,1)'
    return 'block/other-%dcol' % len(act)

def subterms(t):
    if t[0] == 'v':
        return
    yield t
    for u in t[3]:
        yield from subterms(u)

def full_range(t):
    A = infer(G, t)
    if tdim(A) < 1: return False
    B = A
    while tdim(B) > 0:
        B = B[1]
    return B[2] == v(VX[0, 0]) and B[3] == v(VX[2, 2])

# ---------------------------------------------------------------- generated terms
def bracketings(ts):
    if len(ts) == 1:
        yield ts[0]; return
    for i in range(1, len(ts)):
        for l in bracketings(ts[:i]):
            for r in bracketings(ts[i:]):
                yield c0(l, r)

def gen_terms(rng, n):
    pool = []
    for p in ELEMS:
        for q in ELEMS:
            if leq(p, q) and p != q:
                pool.append(N(p, q, lnest_path(p), lnest_path(q)))
    left = [sq(0, 0), c1(kap(c0(h(0, 0), vv(1, 0)), LV[0]), sq(0, 0)), id2(G, LV[0]), id2(G, LV[1])]
    right = [sq(1, 1), c1(sq(1, 1), kap(RV[1], RV[1])), id2(G, RV[0]), id2(G, RV[1])]
    for a in left:
        for b in right:
            pool.append(c0(a, b))
    # exchange orders at a -> c
    pool.append(c1(c0(sq(0, 0), RV[0]), c0(LV[1], sq(1, 1))))
    pool.append(c1(c0(LV[0], sq(1, 1)), c0(sq(0, 0), RV[1])))
    # whiskered chain letters
    pool.append(c0(c0(h(0, 0), sq(1, 0)), vv(2, 1)))
    pool.append(c0(vv(0, 0), c0(sq(0, 1), h(1, 2))))
    out = list(pool)
    tries = 0
    while len(out) < n and tries < 20 * n:
        tries += 1
        t = rng.choice(out)
        A = infer(G, t)
        if tdim(A) != 1: continue
        r = rng.random()
        if r < 0.45:
            u = rng.choice(out)
            Au = infer(G, u)
            if tdim(Au) != 1: continue
            if path(G, A[3])[0] != path(G, Au[2])[0]: continue
            t = c1(c1(t, kap(A[3], Au[2])), u)
        elif r < 0.6:
            t = c0(ident(G, VX[0, 0]), t)
        elif r < 0.75:
            t = c0(t, ident(G, VX[2, 2]))
        else:
            alts = list(bracketings(PATHS[path_elem(path(G, A[2])[0])]))
            alt = rng.choice(alts)
            t = c1(kap(alt, A[2]), t)
        out.append(t)
    return out

# ---------------------------------------------------------------- local cells
P2 = tree_ctx((((),), ((),)))      # x, y1, r0, r1, u, y2, s0, s1, w
def exchange_cells():
    r0, r1, u, s0, s1, w = v(2), v(3), v(4), v(6), v(7), v(8)
    R_GF = comp2(P2, 1, comp2(P2, 0, r0, w), comp2(P2, 0, u, s1))
    R_FG = comp2(P2, 1, comp2(P2, 0, u, s0), comp2(P2, 0, r1, w))
    hz = comp2(P2, 0, u, w)
    ident_sig = tuple(v(i) for i in range(len(P2)))
    chi = full_coh(P2, R_GF, R_FG, ident_sig)
    th_GF = full_coh(P2, R_GF, hz, ident_sig)
    th_FG = full_coh(P2, R_FG, hz, ident_sig)
    route = comp2(P2, 2, chi, th_FG)
    eight = full_coh(P2, route, th_GF, ident_sig)
    sig = sub_from(P2, G, {4: sq(0, 0), 8: sq(1, 1)})
    out = {k: subst_tm(t, sig) for k, t in
           dict(chi=chi, th_GF=th_GF, th_FG=th_FG, eight=eight).items()}
    for t in out.values():
        infer(G, t)
    return out

def raw_law_12():
    """(12) in the block: delta = a -> b, eps = b -> c, eta = id_c.
    Both routes are full over D^2(F) *0 D^2(G); compare them by one coherence,
    formed with formal letters and substituted afterwards."""
    r0, r1, u, s0, s1, w = v(2), v(3), v(4), v(6), v(7), v(8)
    P = P2
    i1 = lambda t: id2(P, t)
    Ed = comp2(P, 0, u, i1(s0)); Ee = comp2(P, 0, i1(r1), w); Eh = comp2(P, 0, i1(r1), i1(s1))
    Ede = comp2(P, 0, u, w)
    def M(Ex, Ey):
        a, b = horiz_factors_P(P, Ex); a_, b_ = horiz_factors_P(P, Ey)
        I = interchange_I(P, a, b, a_, b_)
        return comp2(P, 2, I, comp2(P, 0, unit_cell(P, a, a_), unit_cell(P, b, b_)))
    Meh = M(Ee, Eh)
    Eeh = comp2(P, 0, i1(r1), w)
    # route 1: (M_de *1 Eh) ; M_{de,h};  route 2: assoc ; (Ed *1 M_eh) ; M_{d, eh}
    M_de = M(Ed, Ee)
    rt1 = comp2(P, 2, comp2(P, 1, M_de, Eh), M(Ede, Eh))
    src = comp2(P, 1, comp2(P, 1, Ed, Ee), Eh)
    mid = comp2(P, 1, Ed, comp2(P, 1, Ee, Eh))
    assoc = full_coh(P, src, mid, tuple(v(i) for i in range(len(P))))
    rt2 = vcomp3(P, [assoc, comp2(P, 1, Ed, Meh), M(Ed, Eeh)])
    law = full_coh(P, rt1, rt2, tuple(v(i) for i in range(len(P))))
    sig = sub_from(P, G, {4: sq(0, 0), 8: sq(1, 1), 2: LV[0], 3: LV[1], 6: RV[0], 7: RV[1]})
    out = subst_tm(law, sig)
    infer(G, out)
    return law, out

def horiz_factors_P(P, E):
    _, Q, A, s = E
    mx = maximal_vars(Q)
    return s[mx[0]], s[mx[1]]

P33 = tree_ctx((((), (), ()), ((), (), ())))
def Z3_and_zeta():
    """Z_3 : L *0 R => LF[L1 *0 R1, L2 *0 R2, L3 *0 R3] over C_3 *0 C_3, instantiated
    at the local normal forms of S00 and S11; zeta at a displayed cut."""
    twos = [i for i, A in enumerate(P33) if tdim(A) == 1]
    l, r = twos[:3], twos[3:]
    L_ = lfold(P33, 1, [v(i) for i in l]); R_ = lfold(P33, 1, [v(i) for i in r])
    src = comp2(P33, 0, L_, R_)
    tgt = lfold(P33, 1, [comp2(P33, 0, v(a), v(b)) for a, b in zip(l, r)])
    A0 = c0(h(0, 0), vv(1, 0)); A1 = LV[1]
    lnf = [kap(A0, LV[0]), sq(0, 0), kap(LV[1], A1)]
    B0 = c0(h(1, 1), vv(2, 1)); B1 = c0(vv(1, 1), h(1, 2))
    rnf = [kap(B0, RV[0]), sq(1, 1), kap(RV[1], B1)]
    sig = sub_from(P33, G, dict(zip(l + r, lnf + rnf)))
    Z3 = full_coh(P33, src, tgt, sig)
    infer(G, Z3)
    a, a_ = c0(h(0, 0), vv(1, 0)), LV[0]
    b, b_ = c0(h(1, 1), vv(2, 1)), RV[0]
    zeta = struct_cell(G, kap(c0(a, b), c0(a_, b_)), c0(kap(a, a_), kap(b, b_)))
    return Z3, zeta

def disjoint_interchange():
    """Core of a mixed mu-law: the block merge at the (b, c) junction and the
    separator contraction at the (c, top) junction act at disjoint slots;
    their interchange is one coherence over V(1,1)."""
    Vt = tree_ctx(((((),), ((),)),))
    hs = [i for i, T_ in enumerate(Vt) if tdim(T_) == 2]
    h1, h2 = hs
    a0, a1, b0, b1 = Vt[h1][2], Vt[h1][3], Vt[h2][2], Vt[h2][3]
    rr1 = comp2(Vt, 2, comp2(Vt, 1, v(h1), b0), comp2(Vt, 1, a1, v(h2)))
    rr2 = comp2(Vt, 2, comp2(Vt, 1, a0, v(h2)), comp2(Vt, 1, v(h1), b1))
    q = (1, 0)
    Ed, Ee = E_blk((0, 0), (1, 0)), E_blk((1, 0), (1, 1))
    merge = vcomp3(G, [insert3(G, [Ed, kap(rep(q), rep(q)), Ee], 1, 2,
                                struct_cell(G, kap(rep(q), rep(q)), id2(G, rep(q))))[0],
                       merge_core(Ed, Ee, q)])
    X_ = rep((1, 1)); Y_ = lnest_path((1, 1)); Z_ = infer(G, E_DN)[2]
    contr = struct_cell(G, c1(kap(X_, Y_), kap(Y_, Z_)), kap(X_, Z_))
    sig = sub_from(Vt, G, {h1: merge, h2: contr})
    t = full_coh(Vt, rr1, rr2, sig)
    infer(G, t)
    return t

# ---------------------------------------------------------------- run
def main(n=70, seed=11):
    rng = random.Random(seed)
    ncls = classify()
    nfs = []
    for p in ELEMS:
        for q in ELEMS:
            if leq(p, q):
                nfs.append(((p, q), N(p, q, lnest_path(p), rep(q))))
    mus = []
    for p in ELEMS:
        for q in ELEMS:
            for r in ELEMS:
                if leq(p, q) and leq(q, r):
                    m_, ty = mu(p, q, r, lnest_path(p), lnest_path(q), rep(r))
                    mus.append(((p, q, r), m_, ty))
    nmerge = sum(1 for (k, _, _) in mus
                 if word(k[0], k[1]) and word(k[1], k[2]) and isinstance(word(k[0], k[1])[-1], tuple)
                 and isinstance(word(k[1], k[2])[0], tuple))
    kinds = {}
    facts = []
    seen = set()
    for t in gen_terms(rng, n):
        if t in seen: continue
        seen.add(t)
        for u in subterms(t):
            if full_range(u) and tdim(infer(G, u)) == 1:
                k = head_report(u)
                kinds[k] = kinds.get(k, 0) + 1
        if t[0] == 'coh' and two(G, t):
            R, d, eta, H = factor_cols(G, t)
            R2, d2, e2, H2 = factor_cols(R, H)
            assert R2 == R and H2 == H, 'stability'
            facts.append((t, R, d, eta, H))
    ex = exchange_cells()
    law12_formal, law12 = raw_law_12()
    Z3, zeta = Z3_and_zeta()
    dis = disjoint_interchange()
    for t in list(ex.values()) + [law12, Z3, dis] + [m_ for (_, m_, _) in mus[:8]]:
        for u in subterms(t):
            A = infer(G, u)
            if tdim(A) >= 1 and full_range(u):
                k = head_report(u)
                kinds[k] = kinds.get(k, 0) + 1
    print('grid: strict cells %d (one exchange class each); normal forms %d; mu %d (%d with a block merge); '
          'heads %s; frames %d; exchange + (8), law (12), Z3, zeta, disjoint interchange ok'
          % (ncls, len(nfs), len(mus), nmerge, kinds, len(facts)))
    return nfs, mus, facts, ex, law12, Z3, zeta, dis

def emit_module():
    from emit_agda import Emitter
    nfs, mus, facts, ex, law12, Z3, zeta, dis = main()
    E = Emitter()
    for i, (key, t) in enumerate(nfs):
        E.check_typed('N%d' % i, G, t)
    for i, (key, m_, ty) in enumerate(mus):
        E.check_type('mu%d' % i, G, m_, ty)
    for k_, t in ex.items():
        E.check_typed('ex-' + k_, G, t)
    E.check_typed('law12', G, law12)
    E.check_typed('Z3', G, Z3)
    E.check_typed('zeta', G, zeta)
    E.check_typed('disjoint', G, dis)
    for i, (T_, R, d, e, H) in enumerate(facts):
        E.check_typed('H%d' % i, R, H)
        E.check_typed('eta%d' % i, G, eta_witness(R, e))
        E.check_eq('fact%d' % i, H, e, T_)
    src = E.module('CaTTExp.Generated.GridRC3',
                   'Checks toward RC(3) on the 2 x 2 grid (relative-coherence.md §7.8): normal forms for every interval of the path lattice, the multiplication mu for every composable pair (with block merges), the exchange and its compatibility 4-term, the raw law (12), Z_3, zeta, a disjoint-interchange 4-cell, and frame factorisations. Built by tools/rc3_grid.py.')
    open('../src/CaTTExp/Generated/GridRC3.agda', 'w').write(src)
    print('emitted', len(E.defs), 'definitions,', len(E.checks), 'checks')

def emit_negative():
    """Negative control: mu_{bot,b,top} at its type with source and target swapped."""
    from emit_agda import Emitter
    m_, ty = mu('bot', (1, 0), 'top', lnest_path('bot'), lnest_path((1, 0)), rep('top'))
    E = Emitter(); E.check_type('bad', G, m_, arr(ty[1], ty[3], ty[2]))
    open('../src/CaTTExp/Generated/NegGrid.agda', 'w').write(
        E.module('CaTTExp.Generated.NegGrid', 'Negative control: must be rejected.'))

if __name__ == '__main__':
    import sys
    if sys.argv[1:] == ['emit']:
        emit_module()
    elif sys.argv[1:] == ['neg']:
        emit_negative()
    else:
        main()
