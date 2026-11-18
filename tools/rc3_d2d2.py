"""
Checks toward RC(3) on the 2-skeleton of the cylinder of D^2 *0 D^2
(notes/relative-coherence.md §7.9), and the interchange 4-term (36) of the
round-6 naturality answer on the full cylinder.

    Q = (x, y, f0, f1 : x -> y, A : f0 => f1, z, g0, g1 : y -> z, B : g0 => g1)
    Q^ : x-, x+, X; y-, y+, Yv; f_i-, f_i+, F_i : f_i- *0 Yv => X *0 f_i+;
         A-, A+ (, U_A); z-, z+, Z; g_j-, g_j+, G_j : g_j- *0 Z => Yv *0 g_j+;
         B-, B+ (, U_B).
The 2-skeleton W2 omits U_A, U_B.

Paths x- -> z+ are (i, j, c): R = f_i- g_j- Z, M = f_i- Yv g_j+, L = X f_i+ g_j+.
Factorisation lemma: every strict 2-cell w factors uniquely as w = w1 . w2,
with w1 using only the letters A-, B-, G_j (a product at the cut y-) and w2
only F_i, A+, B+ (a product at the cut y+).  The only exchange needed to
bring a concatenation of two normal forms back to normal form is B+ (in w2)
past A- (in w1'), in phase M: the coherence chi_M over D^2 v D^1 v D^2.

We check:
  * the classification (brute force over 2-paths and exchange classes);
  * normal forms N(w) = kappa . E1(w1) . kappa . E2(w2) . kappa for every
    strict cell from every source path;
  * mu : N(u) . N(v) => N(uv) for every composable pair (block-1 merges,
    block-2 merges, and the chi_M case), typed;
  * chi_M, the transfers between block coordinates, the 3-column fold core;
  * the head-shape lemma on generated terms, and frame factorisations;
  * (36) on the full cylinder.
"""
import random, itertools
from catt import *
from rc2 import struct_cell, ident, path, lfold
from rc3_wedge import factor_cols, eta_witness, two
from rc3_square import column_ranges
from rc3_grid import (id2, CN, zvar, full_coh, reassoc_list, lf_groups, insert3,
                      vcomp3, unit_cell, interchange_I, horiz_factors)

# ---------------------------------------------------------------- the context
def build(full):
    G = []
    ix = {}
    def add(name, ty):
        ix[name] = len(G); G.append(ty)
    def V(n): return v(ix[n])
    for p in 'xy':
        add(p + '-', STAR); add(p + '+', STAR)
        add(p.upper() + 'v', arr(STAR, V(p + '-'), V(p + '+')))
    for i in range(2):
        add('f%d-' % i, arr(STAR, V('x-'), V('y-')))
        add('f%d+' % i, arr(STAR, V('x+'), V('y+')))
        Gt = tuple(G)
        add('F%d' % i, arr(arr(STAR, V('x-'), V('y+')),
                           comp2(Gt, 0, V('f%d-' % i), V('Yv')), comp2(Gt, 0, V('Xv'), V('f%d+' % i))))
    add('A-', arr(arr(STAR, V('x-'), V('y-')), V('f0-'), V('f1-')))
    add('A+', arr(arr(STAR, V('x+'), V('y+')), V('f0+'), V('f1+')))
    if full:
        Gt = tuple(G)
        Lt = comp2(Gt, 1, comp2(Gt, 0, V('A-'), V('Yv')), V('F1'))
        Rt = comp2(Gt, 1, V('F0'), comp2(Gt, 0, V('Xv'), V('A+')))
        add('UA', arr(infer(Gt, Lt), Lt, Rt))
    add('z-', STAR); add('z+', STAR); add('Zv', arr(STAR, V('z-'), V('z+')))
    for j in range(2):
        add('g%d-' % j, arr(STAR, V('y-'), V('z-')))
        add('g%d+' % j, arr(STAR, V('y+'), V('z+')))
        Gt = tuple(G)
        add('G%d' % j, arr(arr(STAR, V('y-'), V('z+')),
                           comp2(Gt, 0, V('g%d-' % j), V('Zv')), comp2(Gt, 0, V('Yv'), V('g%d+' % j))))
    add('B-', arr(arr(STAR, V('y-'), V('z-')), V('g0-'), V('g1-')))
    add('B+', arr(arr(STAR, V('y+'), V('z+')), V('g0+'), V('g1+')))
    if full:
        Gt = tuple(G)
        Lt = comp2(Gt, 1, comp2(Gt, 0, V('B-'), V('Zv')), V('G1'))
        Rt = comp2(Gt, 1, V('G0'), comp2(Gt, 0, V('Yv'), V('B+')))
        add('UB', arr(infer(Gt, Lt), Lt, Rt))
    G = tuple(G)
    check_ctx(G)
    return G, ix

W, IX = build(False)
def x(n): return v(IX[n])
def c0(a, b): return comp2(W, 0, a, b)
def c1(a, b): return comp2(W, 1, a, b)
def kap(a, b): return struct_cell(W, a, b)

# ---------------------------------------------------------------- paths and letters (combinatorial)
def path_names(p):
    i, j, c = p
    return {'R': ['f%d-' % i, 'g%d-' % j, 'Zv'], 'M': ['f%d-' % i, 'Yv', 'g%d+' % j],
            'L': ['Xv', 'f%d+' % i, 'g%d+' % j]}[c]

PATHS = [(i, j, c) for i in range(2) for j in range(2) for c in 'RML']
BACK = {tuple(path_names(p)): p for p in PATHS}
LETTERS = {  # name: (source edges, target edges, block, side)
    'A-': (['f0-'], ['f1-'], 1, 'L'), 'B-': (['g0-'], ['g1-'], 1, 'R'),
    'G0': (['g0-', 'Zv'], ['Yv', 'g0+'], 1, 'R'), 'G1': (['g1-', 'Zv'], ['Yv', 'g1+'], 1, 'R'),
    'F0': (['f0-', 'Yv'], ['Xv', 'f0+'], 2, 'L'), 'F1': (['f1-', 'Yv'], ['Xv', 'f1+'], 2, 'L'),
    'A+': (['f0+'], ['f1+'], 2, 'L'), 'B+': (['g0+'], ['g1+'], 2, 'R'),
}

def apply(pth, name):
    s, t = LETTERS[name][0], LETTERS[name][1]
    for k in range(len(pth) - len(s) + 1):
        if pth[k:k + len(s)] == s:
            return pth[:k] + t + pth[k + len(s):], (k, k + len(s))
    return None

def enumerate_cells():
    """All 2-paths from each source path; exchange classes; check the
    factorisation lemma.  Returns the list of strict cells as
    (p, q, w1L, w1R, w2L, w2R)."""
    cells = {}
    def dfs(p0, cur, w):
        cells.setdefault((p0, BACK[tuple(cur)]), set()).add(tuple(w))
        for nm in LETTERS:
            r = apply(cur, nm)
            if r:
                dfs(p0, r[0], w + [(nm, r[1])])
    for p in PATHS:
        dfs(p, path_names(p), [])
    out = []
    nclasses = 0
    for (p, q), ws in cells.items():
        ws = set(ws)
        # canonical invariant of an exchange class: (block-1 subword by side, block-2 subword by side)
        def split(w):
            names = [n for (n, _) in w]
            b1 = [n for n in names if LETTERS[n][2] == 1]
            b2 = [n for n in names if LETTERS[n][2] == 2]
            return (tuple(n for n in b1 if LETTERS[n][3] == 'L'), tuple(n for n in b1 if LETTERS[n][3] == 'R'),
                    tuple(n for n in b2 if LETTERS[n][3] == 'L'), tuple(n for n in b2 if LETTERS[n][3] == 'R'))
        # exchange classes by connectivity under swaps of adjacent letters acting on disjoint segments
        def swaps(w):
            names = [n for (n, _) in w]
            cur = path_names(p)
            seq = []
            for n in names:
                r = apply(cur, n); seq.append(r[1]); cur = r[0]
            for k in range(len(names) - 1):
                n1, n2 = names[k], names[k + 1]
                (a1, b1) = seq[k]
                (a2, b2) = seq[k + 1]
                d1 = len(LETTERS[n1][1]) - len(LETTERS[n1][0])
                disjoint = (b1 + d1 <= a2) or (b2 <= a1)
                if disjoint:
                    nn = names[:k] + [n2, n1] + names[k + 2:]
                    cur2 = path_names(p); w2 = []
                    ok = True
                    for m in nn:
                        r = apply(cur2, m)
                        if r is None: ok = False; break
                        w2.append((m, r[1])); cur2 = r[0]
                    if ok and BACK[tuple(cur2)] == q:
                        yield tuple(w2)
        seen = set()
        for w in sorted(ws):
            if w in seen: continue
            nclasses += 1
            comp_ = {w}; stack = [w]
            while stack:
                y = stack.pop()
                for z in swaps(y):
                    if z not in comp_:
                        comp_.add(z); stack.append(z)
            seen |= comp_
            inv = {split(y) for y in comp_}
            assert len(inv) == 1, 'class with several invariants'
            blocks = lambda y: [LETTERS[n][2] for (n, _) in y]
            assert any(blocks(y) == sorted(blocks(y)) for y in comp_), 'no block-1-first representative'
            out.append((p, q) + inv.pop())
    keys = [(o[0], o[2], o[3], o[4], o[5]) for o in out]
    assert len(set(keys)) == len(keys), 'two classes with the same factorisation'
    return out

# ---------------------------------------------------------------- terms: representatives and raw letters
def rep1(p):
    i, j, c = p
    assert c in 'RM'
    rt = c0(x('g%d-' % j), x('Zv')) if c == 'R' else c0(x('Yv'), x('g%d+' % j))
    return c0(x('f%d-' % i), rt)

def rep2(p):
    i, j, c = p
    assert c in 'ML'
    lt = c0(x('f%d-' % i), x('Yv')) if c == 'M' else c0(x('Xv'), x('f%d+' % i))
    return c0(lt, x('g%d+' % j))

def raw_local(names):
    """Local raw list for a side word."""
    tm = {'A-': x('A-'), 'B-': c0(x('B-'), x('Zv')), 'G0': x('G0'), 'G1': x('G1'),
          'F0': x('F0'), 'F1': x('F1'), 'A+': c0(x('Xv'), x('A+')), 'B+': x('B+')}
    ls = [tm[n] for n in names]
    out = [ls[0]]
    for e in ls[1:]:
        out.append(kap(infer(W, out[-1])[3], infer(W, e)[2]))
        out.append(e)
    return out

def factor_tm(names, base):
    """The local factor: identity on `base` (a 1-term) or the folded raw list."""
    if not names:
        return id2(W, base)
    return lfold(W, 1, raw_local(names))

def apply_path(p, names):
    cur = path_names(p)
    for n in names:
        cur = apply(cur, n)[0]
    return BACK[tuple(cur)]

def E1(p, wL, wR):
    i, j, c = p
    a = factor_tm(wL, x('f%d-' % i))
    rt = c0(x('g%d-' % j), x('Zv')) if c == 'R' else c0(x('Yv'), x('g%d+' % j))
    b = factor_tm(wR, rt)
    return c0(a, b)

def E2(p, wL, wR):
    i, j, c = p
    lt = c0(x('f%d-' % i), x('Yv')) if c == 'M' else c0(x('Xv'), x('f%d+' % i))
    return c0(factor_tm(wL, lt), factor_tm(wR, x('g%d+' % j)))

def letters_of(cell):
    p, q, w1L, w1R, w2L, w2R = cell
    out = []
    if w1L or w1R:
        out.append(('E1', E1(p, w1L, w1R)))
    m = apply_path(p, list(w1L) + list(w1R))
    if w2L or w2R:
        out.append(('E2', E2(m, w2L, w2R)))
    return out

def N_list(cell, A, B):
    ls = letters_of(cell)
    if not ls:
        return [kap(A, B)]
    out = [kap(A, infer(W, ls[0][1])[2])]
    for k, (_, e) in enumerate(ls):
        out.append(e)
        nxt = infer(W, ls[k + 1][1])[2] if k + 1 < len(ls) else B
        out.append(kap(infer(W, e)[3], nxt))
    return out

def lnest_path(p):
    return lfold(W, 0, [x(n) for n in path_names(p)])

# ---------------------------------------------------------------- local multiplication and merges
def local_mult(a, b):
    """a . b => the canonical local list of the concatenated word."""
    ida = a == id2(W, infer(W, a)[2]); idb = b == id2(W, infer(W, b)[2])
    if ida or idb:
        return unit_cell(W, a, b), (b if ida else a)
    # both non-identity: insert a path comparison between them
    m_ = infer(W, a)[3]
    P = CN(2)
    s = comp2(P, 1, zvar(1), zvar(2))
    t = comp2(P, 1, comp2(P, 1, zvar(1), id2(P, v(3))), zvar(2))
    u = full_coh(P, s, t, sub_from(P, W, {4: a, 6: b}))
    one = id2(W, m_)
    cell2, _ = insert3(W, [a, one, b], 1, 2, struct_cell(W, one, kap(m_, m_)))
    # a, b may themselves be folded lists: reassociate to the flat left fold
    al = flat(a); bl = flat(b)
    L = al + [kap(m_, m_)] + bl
    tgt = lfold(W, 1, L)
    cur = c1(c1(a, kap(m_, m_)), b)
    steps = [u, cell2]
    if cur != tgt:
        steps.append(struct_or_reassoc(cur, L, len(al)))
    return vcomp3(W, steps), tgt

def flat(t):
    """Undo lfold for the raw local lists built here (one level)."""
    for names in (['B-', 'G1'], ['F0', 'A+']):
        L = raw_local(names)
        if t == lfold(W, 1, L):
            return L
    return [t]

def struct_or_reassoc(cur, L, na):
    n = len(L)
    return reassoc_list(W, L, ((tuple(range(na)) if na > 1 else 0, na), tuple(range(na + 1, n)) if n - na - 1 > 1 else n - 1), lf_groups(n))

def block_merge(Ex, Ey):
    a, b = horiz_factors(Ex); a_, b_ = horiz_factors(Ey)
    I = interchange_I(W, a, b, a_, b_)
    mF, ta = local_mult(a, a_)
    mG, tb = local_mult(b, b_)
    return comp2(W, 2, I, comp2(W, 0, mF, mG)), c0(ta, tb)

# ---------------------------------------------------------------- chi_M
PM = tree_ctx((((),), (), ((),)))   # x, y1, f0, f1, a, y2, e, y3, g0, g1, b
def chi_M_formal():
    f0, f1, a, e, g0, g1, b = v(2), v(3), v(4), v(6), v(8), v(9), v(10)
    P = PM
    k = lambda s, t: struct_cell(P, s, t)
    E2s = comp2(P, 0, id2(P, comp2(P, 0, f0, e)), b)                 # (1_{f0 e}) *0 B+
    E1s = comp2(P, 0, a, id2(P, comp2(P, 0, e, g1)))                 # A- *0 1_{e g1}
    E1t = comp2(P, 0, a, id2(P, comp2(P, 0, e, g0)))
    E2t = comp2(P, 0, id2(P, comp2(P, 0, f1, e)), b)
    T2s, S1s = infer(P, E2s)[3], infer(P, E1s)[2]
    src = lfold(P, 1, [E2s, k(T2s, S1s), E1s])
    S2s, T1s = infer(P, E2s)[2], infer(P, E1s)[3]
    tgt = lfold(P, 1, [k(S2s, infer(P, E1t)[2]), E1t, k(infer(P, E1t)[3], infer(P, E2t)[2]), E2t,
                       k(infer(P, E2t)[3], T1s)])
    return src, tgt

def chi_M():
    src, tgt = chi_M_formal()
    sig = sub_from(PM, W, {4: x('A-'), 6: x('Yv'), 10: x('B+')})
    t = full_coh(PM, src, tgt, sig)
    infer(W, t)
    return t

def transfers():
    """Block-1 to block-2 coordinates for B+ and A- in phase M (direct coherences
    over D^1 v D^1 v D^2 and D^2 v D^1 v D^1)."""
    out = {}
    for i in range(2):
        b1 = c0(id2(W, x('f%d-' % i)), c0(x('Yv'), x('B+')))
        b2 = c0(id2(W, c0(x('f%d-' % i), x('Yv'))), x('B+'))
        s1, t1 = infer(W, b1)[2], infer(W, b1)[3]
        s2, t2 = infer(W, b2)[2], infer(W, b2)[3]
        tgt = lfold(W, 1, [kap(s1, s2), b2, kap(t2, t1)])
        out['tauB%d' % i] = (b1, tgt)
    for j in range(2):
        a2 = c0(c0(x('A-'), x('Yv')), id2(W, x('g%d+' % j)))
        a1 = c0(x('A-'), id2(W, c0(x('Yv'), x('g%d+' % j))))
        s1, t1 = infer(W, a2)[2], infer(W, a2)[3]
        s2, t2 = infer(W, a1)[2], infer(W, a1)[3]
        tgt = lfold(W, 1, [kap(s1, s2), a1, kap(t2, t1)])
        out['tauA%d' % j] = (a2, tgt)
    res = {}
    for k_, (s, t) in out.items():
        # both sides are full over the 3-column pasting context of their support
        res[k_] = direct_over_support(s, t)
    return res

def direct_over_support(s, t):
    """A coherence s => t, formed over a pasting context mirroring the support
    (here: a 3-column context with one 2-disc), then substituted."""
    # find the 2-variable used
    twos_ = [i for i in fv_tm(s) if tdim(W[i]) == 1]
    assert len(twos_) == 1
    z = twos_[0]
    col = [n for n in ('A-', 'B+') if IX[n] == z][0]
    if col == 'B+':
        P = tree_ctx(((), (), ((),)))     # x, y1, f, y2, e, y3, g0, g1, b
        names = {2: None, 4: x('Yv'), 8: x('B+')}
        # f is the f_i- edge
        fi = [n for n in ('f0-', 'f1-') if IX[n] in fv_tm(s)][0]
        sig = sub_from(P, W, {2: x(fi), 4: x('Yv'), 8: x('B+')})
        f, e, b = v(2), v(4), v(8)
    else:
        P = tree_ctx((((),), (), ()))     # x, y1, f0, f1, a, y2, e, y3, g
        gj = [n for n in ('g0+', 'g1+') if IX[n] in fv_tm(s)][0]
        sig = sub_from(P, W, {4: x('A-'), 6: x('Yv'), 8: x(gj)})
    # rebuild s, t over P by inverting sig on variables (sig is injective on variables)
    inv = {}
    for k_, tm_ in enumerate(sig):
        assert tm_[0] == 'v'
        inv[tm_[1]] = k_
    rs = rename_back(s, inv); rt = rename_back(t, inv)
    assert subst_tm(rs, sig) == s and subst_tm(rt, sig) == t
    return full_coh(P, rs, rt, sig)

def rename_back(t, inv):
    if t[0] == 'v':
        return v(inv[t[1]])
    return ('coh', t[1], t[2], tuple(rename_back(u, inv) for u in t[3]))

# ---------------------------------------------------------------- mu
def mu(c1_, c2_, A, B, Cc):
    p, q = c1_[0], c1_[1]
    assert c2_[0] == q
    Lu, Lv = N_list(c1_, A, B), N_list(c2_, B, Cc)
    tu, tv = [t for t, _ in letters_of(c1_)], [t for t, _ in letters_of(c2_)]
    m = len(Lu)
    L = Lu + Lv
    lhs = c1(lfold(W, 1, Lu), lfold(W, 1, Lv))
    cells = [reassoc_list(W, L, (tuple(range(m)), tuple(range(m, len(L)))), lf_groups(len(L)))]
    X_ = infer(W, L[m - 1])[2]; Z_ = infer(W, L[m])[3]
    t, L = insert3(W, L, m - 1, m + 1, struct_cell(W, c1(L[m - 1], L[m]), kap(X_, Z_)))
    cells.append(t)
    j = m - 1                                   # junction kappa
    tags = ['k'] + sum([[tg, 'k'] for tg in tu], []) + sum([[tg, 'k'] for tg in tv], [])[0:]
    # rebuild tags after contraction
    tags = (['k'] + sum([[tg, 'k'] for tg in tu], []))[:-1] + ['k'] + sum([[tg, 'k'] for tg in tv], [])
    kind = None
    if j - 1 >= 0 and j + 1 < len(L) and tags[j - 1] != 'k' and tags[j + 1] != 'k':
        kind = (tags[j - 1], tags[j + 1])
    def merge_at(L, j):
        q_ = infer(W, L[j])[2]
        assert L[j] == kap(q_, q_)
        t1, L = insert3(W, L, j, j + 1, struct_cell(W, L[j], id2(W, q_)))
        P = CN(2)
        s = comp2(P, 1, comp2(P, 1, zvar(1), id2(P, v(3))), zvar(2))
        tt = comp2(P, 1, zvar(1), zvar(2))
        u = full_coh(P, s, tt, sub_from(P, W, {4: L[j - 1], 6: L[j + 1]}))
        bm, tgt = block_merge(L[j - 1], L[j + 1])
        t2, L = insert3(W, L, j - 1, j + 2, comp2(W, 2, u, bm))
        return [t1, t2], L
    if kind in (('E1', 'E1'), ('E2', 'E2')):
        ts, L = merge_at(L, j)
        cells += ts
    elif kind == ('E2', 'E1'):
        # chi_M on [E2(B+), kappa, E1(A-)]
        cx = chi_M()
        t, L = insert3(W, L, j - 1, j + 2, cx)
        # unpack the target list of chi_M (5 entries) into the list
        tgt_list = flat_chi_target(cx)
        L = L[:j - 1] + tgt_list + L[j:]
        cells.append(t)
        cells.append(reassoc_list(W, L, regroup(len(L), j - 1, 5), lf_groups(len(L))))
        # contract the kappa pairs on both sides of the moved letters
        X_ = infer(W, L[j - 2])[2]; Z_ = infer(W, L[j - 1])[3]
        t, L = insert3(W, L, j - 2, j, struct_cell(W, c1(L[j - 2], L[j - 1]), kap(X_, Z_)))
        cells.append(t)
        # now [.., E1?, k, E1(A-), k, E2(B+), k, k_after, E2'?..]
        jj = j + 2
        X_ = infer(W, L[jj])[2]; Z_ = infer(W, L[jj + 1])[3]
        t, L = insert3(W, L, jj, jj + 2, struct_cell(W, c1(L[jj], L[jj + 1]), kap(X_, Z_)))
        cells.append(t)
        # merges with neighbours, when present
        if 'E1' in tu:       # E1(w1) . k . E1(A-)
            ts, L = merge_at(L, j - 2)
            cells += ts
            jj -= 2
        if 'E2' in tv:
            ts, L = merge_at(L, jj)
            cells += ts
    res = vcomp3(W, cells)
    ty = infer(W, res)
    assert ty[2] == lhs
    return res, ty, L

def flat_chi_target(cx):
    tgt = infer(W, cx)[3]
    out = []
    t = tgt
    for _ in range(4):
        _, P, A, s = t
        mx = maximal_vars(P)
        out.append(s[mx[1]]); t = s[mx[0]]
    out.append(t)
    return list(reversed(out))

def regroup(n, i, k):
    return tuple(range(i)) + (tuple(range(i, i + k)),) + tuple(range(i + k, n))

def compose(c1_, c2_):
    p, q, a1, b1, a2, b2 = c1_
    _, r, a1_, b1_, a2_, b2_ = c2_
    # the composite's factorisation: block-1 letters of both, then block-2 letters of both
    return (p, r, a1 + a1_, b1 + b1_, a2 + a2_, b2 + b2_)

# ---------------------------------------------------------------- generated terms, heads
def edge_src(e): return W[e][2][1]

def head_report(t):
    _, P, _A, g = t
    B = infer(W, t)
    while tdim(B) > 1:
        B = B[1]
    sw, a, b = path(W, B[2]); tw, _, _ = path(W, B[3])
    sv = [edge_src(e) for e in sw] + [b]; tv = [edge_src(e) for e in tw] + [b]
    common = set(sv) & set(tv)
    cols = column_ranges(tree_of(P))
    verts = [g[0][1]] + [g[s1][1] for (_, s1, _, _) in cols]
    assert all(z in common for z in verts), 'arity vertex not common'
    act = [k for k, (s0, s1, f, e) in enumerate(cols) if any(two(W, g[i]) for i in range(f, e))]
    if common == {IX['x-'], IX['z+']} and sw != tw:
        assert len(act) == 1, 'prime value with %d active columns' % len(act)
        return 'prime-1col'
    cuts = [g[cols[k][1]][1] for k in act[:-1]]
    for c in cuts:
        assert c in (IX['y-'], IX['y+']), 'active columns split outside y-, y+'
    return '%dcol' % len(act)

def subterms(t):
    if t[0] == 'v': return
    yield t
    for u in t[3]:
        yield from subterms(u)

def full_range(t):
    B = infer(W, t)
    if tdim(B) < 1: return False
    while tdim(B) > 0:
        B = B[1]
    return B[2] == x('x-') and B[3] == x('z+')

def gen_terms(rng, n, cells):
    pool = []
    for cell in cells:
        p, q = cell[0], cell[1]
        pool.append(lfold(W, 1, N_list(cell, lnest_path(p), lnest_path(q))))
    # horizontal composites at y- and y+, three columns in phase M
    for i in range(2):
        for j in range(2):
            pool.append(c0(x('A-'), x('G%d' % j)) if i == 0 else c0(id2(W, x('f1-')), x('G%d' % j)))
            pool.append(c0(x('F%d' % i), x('B+')))
            pool.append(c0(x('A-'), c0(x('Yv'), x('B+'))))
            pool.append(c0(c0(x('A-'), x('Yv')), x('B+')))
    pool.append(c1(c0(c0(x('f0-'), x('Yv')), x('B+')), c0(c0(x('A-'), x('Yv')), x('g1+'))))
    out = list(pool)
    tries = 0
    while len(out) < n and tries < 30 * n:
        tries += 1
        t = rng.choice(out)
        A = infer(W, t)
        if tdim(A) != 1: continue
        r = rng.random()
        if r < 0.5:
            u = rng.choice(out)
            Au = infer(W, u)
            if tdim(Au) != 1 or path(W, A[3])[0] != path(W, Au[2])[0]: continue
            t = c1(c1(t, kap(A[3], Au[2])), u)
        elif r < 0.65:
            t = c0(ident(W, IX['x-']), t)
        elif r < 0.8:
            t = c0(t, ident(W, IX['z+']))
        else:
            alt = lfold(W, 0, [v(e) for e in path(W, A[2])[0]])
            t = c1(kap(alt, A[2]), t)
        out.append(t)
    return out

# ---------------------------------------------------------------- (36) on the full cylinder
def eq36():
    Wf, IXf = build(True)
    X = lambda n: v(IXf[n])
    cf0 = lambda a, b: comp2(Wf, 0, a, b)
    Vb = cf0(X('f0-'), X('UB'))
    Ua = cf0(X('UA'), X('g1+'))
    s_V, t_V = infer(Wf, Vb)[2], infer(Wf, Vb)[3]
    s_U, t_U = infer(Wf, Ua)[2], infer(Wf, Ua)[3]
    # 1-boundaries at the interface: target 1-cell of t_V and source 1-cell of s_U
    K = struct_cell(Wf, infer(Wf, t_V)[3], infer(Wf, s_U)[2])
    P = tree_ctx(((((),),), ((),), (((),),)))    # D^3 *1 D^2 *1 D^3 (one 1-column)
    P = tree_ctx(((((),), ((),), ((),)),))
    # build D^3(v) *1 D^2(k) *1 D^3(u): one 0-column, three 2-slots, the outer two with a 3-cell
    P = tree_ctx(((((),), (), ((),)),))
    threes = [i for i, A in enumerate(P) if tdim(A) == 2]
    twos = [i for i, A in enumerate(P) if tdim(A) == 1]
    hv, hu = threes
    sv_, tv_ = P[hv][2], P[hv][3]
    su_, tu_ = P[hu][2], P[hu][3]
    k_ = [v(i) for i in twos if v(i) not in (sv_, tv_, su_, tu_)][0]
    R1 = comp2(P, 2, comp2(P, 1, comp2(P, 1, v(hv), k_), su_), comp2(P, 1, comp2(P, 1, tv_, k_), v(hu)))
    R2 = comp2(P, 2, comp2(P, 1, comp2(P, 1, sv_, k_), v(hu)), comp2(P, 1, comp2(P, 1, v(hv), k_), tu_))
    sig = sub_from(P, Wf, {hv: Vb, hu: Ua, k_[1]: K})
    t = full_coh(P, R1, R2, sig)
    infer(Wf, t)
    return Wf, t

# ---------------------------------------------------------------- run
def main(n=70, seed=13):
    rng = random.Random(seed)
    cells = enumerate_cells()
    nfs = [(c, lfold(W, 1, N_list(c, lnest_path(c[0]), rep_any(c[1])))) for c in cells]
    mus = []
    kinds = {'E1E1': 0, 'E2E2': 0, 'chi': 0, 'sep': 0}
    for c1_ in cells:
        for c2_ in cells:
            if c2_[0] != c1_[1]: continue
            comp_ = compose(c1_, c2_)
            assert comp_ in cells, ('composite not a listed strict cell', c1_, c2_)
            res, ty, L = mu(c1_, c2_, lnest_path(c1_[0]), lnest_path(c1_[1]), rep_any(c2_[1]))
            want = lfold(W, 1, N_list(comp_, lnest_path(c1_[0]), rep_any(c2_[1])))
            assert ty[3] == want, ('mu target', c1_, c2_)
            tu = [t for t, _ in letters_of(c1_)]; tv = [t for t, _ in letters_of(c2_)]
            k = 'sep'
            if tu and tv:
                k = {('E1', 'E1'): 'E1E1', ('E2', 'E2'): 'E2E2', ('E2', 'E1'): 'chi'}.get((tu[-1], tv[0]), 'sep')
            kinds[k] += 1
            mus.append(((c1_, c2_), res, ty))
    hk = {}
    facts = []
    seen = set()
    for t in gen_terms(rng, n, cells):
        if t in seen: continue
        seen.add(t)
        for u in subterms(t):
            if full_range(u):
                k = head_report(u); hk[k] = hk.get(k, 0) + 1
        if t[0] == 'coh' and two(W, t):
            R, d, eta, H = factor_cols(W, t)
            facts.append((t, R, d, eta, H))
    cx = chi_M()
    tr = transfers()
    Wf, e36 = eq36()
    print('D2*0D2 2-skeleton: strict cells %d (each = w1.w2, unique); normal forms %d; mu %d %s; '
          'heads %s; frames %d; chi_M, %d transfers, (36) ok'
          % (len(cells), len(nfs), len(mus), kinds, hk, len(facts), len(tr)))
    return cells, nfs, mus, facts, cx, tr, (Wf, e36)

def rep_any(p):
    return rep1(p) if p[2] in 'RM' else rep2(p)

def emit_module(max_mu=None):
    from emit_agda import Emitter
    cells, nfs, mus, facts, cx, tr, (Wf, e36) = main()
    E = Emitter()
    for i, (c, t) in enumerate(nfs):
        E.check_typed('N%d' % i, W, t)
    sel = mus if max_mu is None else mus[:max_mu]
    for i, (key, m_, ty) in enumerate(sel):
        E.check_type('mu%d' % i, W, m_, ty)
    E.check_typed('chiM', W, cx)
    for k_, t in tr.items():
        E.check_typed(k_, W, t)
    E.check_typed('eq36', Wf, e36)
    for i, (T_, R, d, e, H) in enumerate(facts):
        E.check_typed('H%d' % i, R, H)
        E.check_typed('eta%d' % i, W, eta_witness(R, e))
        E.check_eq('fact%d' % i, H, e, T_)
    src = E.module('CaTTExp.Generated.TwoDiscCylinderRC3',
                   'Checks toward RC(3) on the 2-skeleton of the cylinder of D^2 *0 D^2 (relative-coherence.md §7.9): normal forms of every strict cell, the multiplication mu for every composable pair (block merges and the exchange chi_M), the block transfers, frame factorisations, and (36) on the full cylinder. Built by tools/rc3_d2d2.py.')
    open('../src/CaTTExp/Generated/TwoDiscCylinderRC3.agda', 'w').write(src)
    print('emitted', len(E.defs), 'definitions,', len(E.checks), 'checks')

def emit_negative():
    from emit_agda import Emitter
    cx = chi_M(); A = infer(W, cx)
    E = Emitter(); E.check_type('bad', W, cx, arr(A[1], A[3], A[2]))
    open('../src/CaTTExp/Generated/NegTwoDisc.agda', 'w').write(
        E.module('CaTTExp.Generated.NegTwoDisc', 'Negative control: must be rejected.'))

if __name__ == '__main__':
    import sys
    if sys.argv[1:] == ['emit']:
        emit_module()
    elif sys.argv[1:] == ['neg']:
        emit_negative()
    else:
        main()
