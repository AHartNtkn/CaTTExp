"""
Rank >= 3 comparisons for rc_oracle.rc that are not the r9 Response 15
descent: three local reductions, each followed by a single coherence on a
pasting context. Like the rest of the oracle they are untrusted (every
answer is type-checked) and not complete; a query they do not reduce gets
no answer.

  slot_norm    top-slot congruence. In a composition head coh_P(B)[s] of
               dimension N, each argument at an N-dimensional position is
               normalized recursively, and an argument whose strict image is
               an identity is compared with the identity coherence on its
               source. All changed slots are carried by ONE coherence over
               P'' (P with each changed top variable a given a parallel copy
               a' and a cell a -> a'), which is a pasting context of
               dimension N+1 with the old term on its source boundary and the
               new term on its target boundary.
  abstract     replace every maximal coherence subterm of dimension <= d
               (and those in the types they need) by a fresh variable. The
               result is a substitution instance of a query over a smaller
               context G'; if G' is a pasting context up to renumbering one
               coherence answers it, otherwise rc recurses on G' when G' has
               fewer variables than G.
  (peel)       the common-factor reduction of rc_oracle, rerun on the
               normalized terms.

`heur(G, A, t, u, rec)` composes: t -> slot_norm(t), the core comparison,
slot_norm(u) -> u. `rec` is the oracle (rc_oracle._rc_inner).
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from catt import *


def _R():
    import rc_oracle
    return rc_oracle

# ---------------------------------------------------------------- pasting-tree surgery

def _paths(tree):
    """For tree_ctx(tree): the tree path of the node whose edge each variable
    is (None for objects)."""
    out = [None]
    def emit(node, path):
        for i, child in enumerate(node):
            out.append(None)                # target object
            out.append(path + (i,))         # edge
            emit(child, path + (i,))
    emit(tree, ())
    return out

def _grow(tree, path):
    """Give the leaf at `path` one leaf child."""
    if not path:
        assert tree == (), 'not a leaf'
        return ((),)
    i = path[0]
    return tree[:i] + (_grow(tree[i], path[1:]),) + tree[i + 1:]

def congruence(G, t, new, forward=True):
    """t = coh_P(B)[s] a composition head of dimension N; new = {i: (s_i', W_i)}
    for top positions i, with W_i : s[i] -> s_i' if forward else s_i' -> s[i].
    Returns the coherence t -> t' (forward) or t' -> t (backward), t' the
    head with the new arguments."""
    _, P, B, s = t
    N = tdim(B) + 1
    tree = tree_of(P)
    paths = _paths(tree)
    T2 = tree
    for i in sorted(new, key=lambda i: paths[i], reverse=True):
        T2 = _grow(T2, paths[i])
    P2 = tree_ctx(T2)
    lo, li = restrict(P2, ps_boundary_vars(P2, N, '-'))
    hi, hj = restrict(P2, ps_boundary_vars(P2, N, '+'))
    assert lo == P and hi == P, 'congruence: boundary is not P'
    src_ = ('coh', P, B, li)
    tgt_ = ('coh', P, B, hj)
    # images of P2's maximal variables
    W_of = {}
    for j, C in enumerate(P2):
        if tdim(C) + 1 == N + 1:
            W_of[C[2][1]] = j
    images = {}
    s_new = list(s)
    for i in range(len(P)):
        a = li[i][1]
        if i in new:
            si2, Wi = new[i]
            s_new[i] = si2
            images[W_of[a]] = Wi
            if not forward:
                # P2's source copy carries the new argument, its target the old
                images[a] = si2
                images[hj[i][1]] = s[i]
            else:
                images[a] = s[i]
                images[hj[i][1]] = si2
        else:
            images[a] = s[i]
    sub = sub_from(P2, G, images)
    A2 = infer(P2, src_)
    return ('coh', P2, arr(A2, src_, tgt_), sub), ('coh', P, B, tuple(s_new))

# ---------------------------------------------------------------- top-slot normalization

def is_identity_value(G, t):
    return _R()._top_cached(G, t) == ()

def slot_norm(G, t, forward, rec):
    """(t', C) with C : t -> t' (forward) or t' -> t, None when t' == t."""
    R = _R()
    if t[0] == 'v':
        return t, None
    _, P, B, s = t
    N = tdim(B) + 1
    if ps_dim(P) != N:
        return t, None
    new = {}
    for i, C in enumerate(P):
        if tdim(C) + 1 != N:
            continue
        a = s[i]
        a2, Ca = slot_norm(G, a, forward, rec)
        Ta = infer(G, a)
        if is_identity_value(G, a) and Ta[2] == Ta[3]:
            idt = R.identity(G, infer(G, a)[2])
            if a2 != idt:
                X = rec(G, infer(G, a), a2, idt) if forward else rec(G, infer(G, a), idt, a2)
                if X is not None:
                    Ca = X if Ca is None else (comp2(G, N, Ca, X) if forward else comp2(G, N, X, Ca))
                    a2 = idt
        if Ca is not None:
            new[i] = (a2, Ca)
    C = None
    t2 = t
    if new:
        C, t2 = congruence(G, t, new, forward)
    t3, D = distribute(G, t2, forward)
    if D is not None:
        C = D if C is None else (comp2(G, N, C, D) if forward else comp2(G, N, D, C))
    return t3, C

def _shift_path(p, parent, i0, k):
    if len(p) > len(parent) and p[:len(parent)] == parent and p[len(parent)] > i0:
        return p[:len(parent)] + (p[len(parent)] + k - 1,) + p[len(parent) + 1:]
    return p

def _replace_leaf(tree, path, k):
    if len(path) == 1:
        i = path[0]
        assert tree[i] == ()
        return tree[:i] + ((),) * k + tree[i + 1:]
    i = path[0]
    return tree[:i] + (_replace_leaf(tree[i], path[1:], k),) + tree[i + 1:]

def _split_leaves(tree, leaves, k):
    """Replace each leaf whose path is in `leaves` by k sibling leaves.
    Returns (new tree, {old path: new path} for the other nodes,
    {old leaf path: [new sibling paths]})."""
    pmap, smap = {}, {}
    def go(node, old, new):
        out = []
        for i, child in enumerate(node):
            op = old + (i,)
            if op in leaves:
                assert child == ()
                smap[op] = [new + (len(out) + j,) for j in range(k)]
                out += [()] * k
            else:
                np_ = new + (len(out),)
                pmap[op] = np_
                out.append(go(child, op, np_))
        return tuple(out)
    return go(tree, (), ()), pmap, smap

def distribute(G, t, forward):
    """If t = H(..., c_i, ...) where every argument c_i at an N-dimensional
    position of H's pasting context is a composite of the same number k >= 2
    of factors along N-1, return (H(f_1) * ... * H(f_k), D) with H(f_j) taking
    the j-th factor in every such slot (interchange), and D : t -> that
    (forward) or back. One coherence over P^k, H's pasting context with each
    of those leaves replaced by k sibling leaves."""
    R = _R()
    if t[0] != 'coh':
        return t, None
    _, P, B, s = t
    N = tdim(B) + 1
    tops = [i for i, C in enumerate(P) if tdim(C) + 1 == N]
    if ps_dim(P) != N or not tops:
        return t, None
    fss = {i: R.vfactors(G, s[i], N) for i in tops}
    k = len(fss[tops[0]])
    if k < 2 or any(len(fs) != k for fs in fss.values()):
        return t, None
    tree = tree_of(P)
    paths = _paths(tree)
    parents = [paths[i][:-1] for i in tops]
    if len(set(parents)) != len(parents):
        return t, None                  # two top slots composable along N-1
    Tk, pmap, smap = _split_leaves(tree, {paths[i] for i in tops}, k)
    Pk = tree_ctx(Tk)
    var_at = {p: j for j, p in enumerate(_paths(Tk)) if p is not None}
    sib = {i: [var_at[q] for q in smap[paths[i]]] for i in tops}
    mx = maximal_vars(P)
    other = {m: v(var_at[pmap[paths[m]]]) for m in mx if m not in sib}
    def iota(j):
        im = dict(other)
        for i in tops:
            im[i] = v(sib[i][j])
        return sub_from(P, Pk, im)
    Hs = [('coh', P, B, iota(j)) for j in range(k)]
    rhs = R.vcomp_over_terms(Pk, N, Hs)
    # each slot argument, with its own bracketing, over Pk
    Ck, ctops = R.column(N, k)
    im = dict(other)
    for i in tops:
        try:
            Tc = R._abstract(G, s[i], N, Ck, ctops, [0])
        except TypeError_:
            return t, None          # the slot is not literally a column
        to_pk = sub_from(Ck, Pk, {ctops[j]: v(sib[i][j]) for j in range(k)})
        im[i] = subst_tm(Tc, to_pk)
    lhs = ('coh', P, B, sub_from(P, Pk, im))
    gim = {}
    for m in mx:
        if m in sib:
            for j in range(k):
                gim[sib[m][j]] = fss[m][j]
        else:
            gim[other[m][1]] = s[m]
    sk = sub_from(Pk, G, gim)
    A = infer(Pk, lhs)
    D = ('coh', Pk, arr(A, lhs, rhs), sk) if forward else ('coh', Pk, arr(A, rhs, lhs), sk)
    t2 = subst_tm(rhs, sk)
    assert subst_tm(lhs, sk) == t, 'distribute: lhs does not instantiate to t'
    return t2, D

# ---------------------------------------------------------------- abstraction

def _abstract_once(G, A, t, u, d, keep):
    newctx, sub, var_of, term_of = [], [], {}, {}
    def tm(x):
        if x[0] == 'v':
            j = x[1]
            if j not in var_of:
                T = ty(G[j])
                var_of[j] = len(newctx)
                newctx.append(T); sub.append(x)
            return v(var_of[j])
        D = tdim(infer(G, x)) + 1
        if D <= d and x not in keep:
            if x not in term_of:
                T = ty(infer(G, x))
                term_of[x] = len(newctx)
                newctx.append(T); sub.append(x)
            return v(term_of[x])
        _, P, B, s = x
        return ('coh', P, B, tuple(tm(a) for a in s))
    def ty(B):
        if B == STAR:
            return B
        return arr(ty(B[1]), tm(B[2]), tm(B[3]))
    A2, t2, u2 = ty(A), tm(t), tm(u)
    return tuple(newctx), tuple(sub), A2, t2, u2

def _coh_subterms(G2, A):
    out = []
    def tm(x):
        if x[0] == 'coh':
            out.append(x)
            for a in x[3]:
                tm(a)
    while A != STAR:
        tm(A[2]); tm(A[3]); A = A[1]
    return out

def abstract(G, A, t, u, d):
    """(G', s, A', t', u') with s : G' -> G a substitution, A'[s] = A etc.,
    abstracting maximal coherence subterms of dimension <= d. A subterm that
    the type of a head computes (so that abstracting it would break typing)
    is kept and abstracted inside instead. None if no well-typed result."""
    keep = set()
    for _ in range(64):
        G2, sub, A2, t2, u2 = _abstract_once(G, A, t, u, d, keep)
        bad = set()
        try:
            check_ctx(G2)
            for x in (t2, u2):
                B = infer(G2, x)
                if B != A2:
                    bad |= {subst_tm(z, sub) for z in _coh_subterms(G2, B)}
        except (TypeError_, AssertionError, KeyError):
            return None
        if not bad:
            return G2, sub, A2, t2, u2
        if bad <= keep:
            return None
        keep |= bad
    return None

def via_abstraction(G, A, t, u, rec):
    R = _R()
    n = tdim(A) + 1
    for d in range(n - 1, -1, -1):
        r = abstract(G, A, t, u, d)
        if r is None:
            continue
        G2, s, A2, t2, u2 = r
        if R.strict_image(G2, t2) != R.strict_image(G2, u2):
            continue
        H, incl, AH, tH, uH = R.restrict_to(G2, A2, t2, u2)
        w = R.globular_comparison(H, AH, tH, uH)
        if w is None and len(H) < len(G):
            w = rec(H, AH, tH, uH)
        if w is not None:
            return subst_tm(subst_tm(w, incl), s)
    return None

def rebracket(G, A, t, u):
    """t and u have the same top-cut factors and differ in bracketing: one
    coherence over the column context."""
    R = _R()
    n = tdim(A) + 1
    ft, fu = R.vfactors(G, t, n), R.vfactors(G, u, n)
    if ft != fu or len(ft) < 2:
        return None
    C, tops = R.column(n, len(ft))
    sub = sub_from(C, G, {tops[j]: ft[j] for j in range(len(ft))})
    Tt = R._abstract(G, t, n, C, tops, [0])
    Tu = R._abstract(G, u, n, C, tops, [0])
    return ('coh', C, arr(infer(C, Tt), Tt, Tu), sub)

def cancel_loop(G, A, x, fw, rec):
    """x a vertical composite H(f_1) * ... * H(f_k) (k >= 2) of one composition
    head H with a single top slot, whose ends agree and whose slot composite
    c = f_1 * ... * f_k has identity value with equal ends (for example a
    coherence followed by its inverse). Returns x -> 1 (fw) or 1 -> x:
    regroup into H(c) (distribution backwards), compare c with the identity
    recursively, then H(1) with the identity recursively."""
    R = _R()
    n = tdim(A) + 1
    if A[2] != A[3]:
        return None
    fs = R.vfactors(G, x, n)
    if len(fs) < 2 or any(f[0] != 'coh' for f in fs):
        return None
    _, P, B, s0 = fs[0]
    if any((f[1], f[2]) != (P, B) for f in fs) or ps_dim(P) != n:
        return None
    tops = [i for i, C in enumerate(P) if tdim(C) + 1 == n]
    if len(tops) != 1:
        return None
    i = tops[0]
    mx = maximal_vars(P)
    if any(f[3][m] != s0[m] for f in fs for m in mx if m != i):
        return None
    c = R.vcomp_over_terms(G, n, [f[3][i] for f in fs])
    Tc = infer(G, c)
    if Tc[2] != Tc[3] or not is_identity_value(G, c):
        return None
    h = ('coh', P, B, sub_from(P, G, {**{m: s0[m] for m in mx if m != i}, i: c}))
    col, D = distribute(G, h, not fw)          # fw: D : col -> h
    if D is None:
        return None
    rb = None
    if col != x:
        rb = rebracket(G, A, x, col) if fw else rebracket(G, A, col, x)
        if rb is None:
            return None
    idc = R.identity(G, Tc[2])
    X1 = rec(G, Tc, c, idc) if fw else rec(G, Tc, idc, c)
    if X1 is None:
        return None
    Cg, h1 = congruence(G, h, {i: (idc, X1)}, fw)
    idt = R.identity(G, A[2])
    X2 = (rec(G, A, h1, idt) if fw else rec(G, A, idt, h1)) if h1 != idt else None
    if h1 != idt and X2 is None:
        return None
    cells = [rb, D, Cg, X2] if fw else [X2, Cg, D, rb]
    cells = [y for y in cells if y is not None]
    out = cells[0]
    for y in cells[1:]:
        out = comp2(G, n, out, y)
    return out

# ---------------------------------------------------------------- driver

def _subst_diff(a, b, acc):
    """Collect (y, Z) where a has the variable y and b has Z != v(y) at the
    same position; False if a and b differ in shape elsewhere."""
    if a == b:
        return True
    if a[0] == 'v':
        acc.add((a[1], b)); return True
    if b[0] == 'v' or a[1] != b[1] or a[2] != b[2] or len(a[3]) != len(b[3]):
        return False
    return all(_subst_diff(x, y, acc) for x, y in zip(a[3], b[3]))

def interchange(G, A, t, u, rec):
    """Interchange of two events. If, after a common prefix, t has factors
    [f, g] and u has [g', f'], where f' is f with one variable y replaced by
    Z and e : y -> Z is a context cell, the naturality square of f along e
    at y (rc_nat.square) goes from f * (tau f)^ to (sigma f)^ * f'. It is
    whiskered by the rest of t, and both of its ends are compared to t and
    u by `rec`."""
    R = _R()
    import rc_nat as N
    n = tdim(A) + 1
    ft, fu = R.vfactors(G, t, n), R.vfactors(G, u, n)
    for i in range(min(len(ft), len(fu)) - 1):
        if ft[i] == fu[i]:
            continue
        if ft[:i] != fu[:i]:
            return None
        f, f2 = ft[i], fu[i + 1]
        acc = set()
        if not _subst_diff(f, f2, acc) or len(acc) != 1:
            return None
        y, Z = next(iter(acc))
        es = [k for k, T in enumerate(G) if T != STAR and T[2] == v(y) and T[3] == Z]
        if not es:
            return None
        try:
            w, a, b = N.square(G, {y}, {y: Z}, {y: v(es[0])}, f, rec)
        except (N.NoFiller, TypeError_, AssertionError, KeyError, ValueError):
            return None
        pre, post = ft[:i], ft[i + 2:]
        W = w
        if post:
            W = comp2(G, n - 1, W, R.vcomp_over_terms(G, n, post))
        if pre:
            W = comp2(G, n - 1, R.vcomp_over_terms(G, n, pre), W)
        s_, t_ = src(G, W), tgt(G, W)
        cells = []
        if s_ != t:
            x = rec(G, A, t, s_)
            if x is None:
                return None
            cells.append(x)
        cells.append(W)
        if t_ != u:
            x = rec(G, A, t_, u)
            if x is None:
                return None
            cells.append(x)
        out = cells[0]
        for c in cells[1:]:
            out = comp2(G, n, out, c)
        return out
    return None

def _events(G, f, n):
    """The n-variables occurring in f."""
    return sorted(i for i in fv_tm(f) if G[i] != STAR and tdim(G[i]) + 1 == n)

def _vc_or_id(G, n, fs, face):
    R = _R()
    if not fs:
        return R.identity(G, face)
    return R.vcomp_over_terms(G, n, fs)

def _segments(G, A, t, u, segt, segu, rec, given=None):
    """t, u with top-cut factor lists split into the same number of
    segments segt[k], segu[k] (lists, possibly empty) with matching ends.
    Compares segment by segment, whiskering each comparison by the others
    (empty segments contribute nothing), with `rec` for the bracketing and
    unit changes at the two ends."""
    R = _R()
    n = tdim(A) + 1
    K = len(segt)
    def faces(segs):
        out, face = [], A[2]
        for sg in segs:
            out.append(face)
            if sg:
                face = tgt(G, sg[-1])
        return out
    def chain(ws):
        ws = [w for w in ws if w is not None]
        w = ws[-1]
        for x in reversed(ws[:-1]):
            w = comp2(G, n - 1, x, w)
        return w
    def term(segs):
        parts = [R.vcomp_over_terms(G, n, sg) if sg else None for sg in segs]
        if all(p is None for p in parts):
            return R.identity(G, A[2]), parts
        return chain(parts), parts
    cur_segs = list(segt)
    T0, _ = term(cur_segs)
    steps = []
    if T0 != t:
        x = rec(G, A, t, T0)
        if x is None:
            return None
        steps.append(x)
    for k in range(K):
        if segt[k] == segu[k]:
            continue
        Tk, parts = term(cur_segs)
        fk = faces(cur_segs)[k]
        a = parts[k] if parts[k] is not None else R.identity(G, fk)
        nxt = list(cur_segs); nxt[k] = segu[k]
        Tk2, parts2 = term(nxt)
        b = parts2[k] if parts2[k] is not None else R.identity(G, fk)
        X = given[k] if given and k in given else rec(G, infer(G, a), a, b)
        if X is None:
            return None
        W = chain(parts[:k] + [X] + parts[k + 1:])
        if src(G, W) != Tk or tgt(G, W) != Tk2:
            x0 = rec(G, A, Tk, src(G, W)) if src(G, W) != Tk else None
            x1 = rec(G, A, tgt(G, W), Tk2) if tgt(G, W) != Tk2 else None
            if (src(G, W) != Tk and x0 is None) or (tgt(G, W) != Tk2 and x1 is None):
                return None
            W = chain3(G, n, x0, W, x1)
        steps.append(W)
        cur_segs = nxt
    T1, _ = term(cur_segs)
    if T1 != u:
        x = rec(G, A, T1, u)
        if x is None:
            return None
        steps.append(x)
    if not steps:
        return R.identity(G, t)
    out = steps[0]
    for y in steps[1:]:
        out = comp2(G, n, out, y)
    return out

def chain3(G, n, x0, W, x1):
    out = W
    if x0 is not None:
        out = comp2(G, n, x0, out)
    if x1 is not None:
        out = comp2(G, n, out, x1)
    return out

def _split_nested(G, h, n, order_key, i, tops):
    """All events of h lie in the top slot i: split that argument
    recursively into c_1 * ... * c_k, pad the other top slots with
    identities, and distribute."""
    R = _R()
    import rc_inverse as I
    _, P, B, s = h
    c = s[i]
    fc = R.vfactors(G, c, n)
    if len(fc) == 1:
        r = _split_factor(G, c, n, order_key)
        if r is None:
            return None
        cseq, Dc = r
    else:
        cseq, Dc = c, None
    cf = R.vfactors(G, cseq, n)
    k = len(cf)
    if k < 2:
        return None
    new = {}
    if Dc is not None:
        new[i] = (cseq, Dc)
    fss = {i: cf}
    for j in tops:
        if j == i:
            continue
        d = s[j]
        one = R.identity(G, tgt(G, d))
        pad = [d] + [one] * (k - 1)
        dp = R.vcomp_over_terms(G, n, pad)
        Wd = _R()._rc_inner(G, infer(G, d), d, dp)
        if Wd is None:
            return None
        new[j] = (dp, Wd)
        fss[j] = pad
    steps = []
    h1 = h
    if new:
        Cg, h1 = congruence(G, h, new, True)
        steps.append(Cg)
    col, D = I._distribute_pairs(G, h1, fss, True)
    if D is None:
        return None
    steps.append(D)
    out = steps[0]
    for y in steps[1:]:
        out = comp2(G, n, out, y)
    return col, out

def _split_general(G, h, n, order_key, coh_key=None):
    """h = H(.., c_i, ..) a composition head of dimension n whose top slots
    carry several events, some slot possibly several (nested). Each slot is
    cut into chunks with one event each (its own split when it is a single
    factor with several events; coherence factors ride with the preceding
    chunk), the chunks of all slots are ordered by order_key, every slot is
    padded with identities to the common length, and H is distributed over
    the padded slots. Returns (seq, D) with D : h -> seq."""
    R = _R()
    import rc_inverse as I
    if h[0] != 'coh':
        return None
    _, P, B, s = h
    if tdim(B) + 1 != n or ps_dim(P) != n:
        return None
    tops = [i for i, C in enumerate(P) if tdim(C) + 1 == n]
    chunks, pre = {}, {}
    for i in tops:
        c = s[i]
        if not _events(G, c, n):
            if coh_key is not None and c != R.identity(G, src(G, c)):
                chunks[i] = [c]
            continue
        fc = R.vfactors(G, c, n)
        if len(fc) == 1 and len(_events(G, c, n)) >= 2:
            r = _split_factor(G, c, n, order_key)
            if r is None:
                return None
            pre[i] = r
            fc = R.vfactors(G, r[0], n)
        ch = []
        for f in fc:
            if _events(G, f, n) or not ch:
                ch.append([f])
            else:
                ch[-1].append(f)
        if len(ch) > 1 and not any(_events(G, f, n) for f in ch[0]):
            ch[1] = ch[0] + ch[1]
            ch = ch[1:]
        chunks[i] = [R.vcomp_over_terms(G, n, c_) if len(c_) > 1 else c_[0] for c_ in ch]
    allc = []
    for i in chunks:          # keys made monotone along each slot's own order
        m = None
        for k, c_ in enumerate(chunks[i]):
            key = order_key(c_) if _events(G, c_, n) else coh_key
            m = key if m is None or key > m else m
            allc.append(((m, k), i, k))
    allc.sort()
    K = len(allc)
    if K < 2:
        return None
    fss, new = {}, {}
    for i in tops:
        if i not in chunks:
            d = s[i]
            pad = [d] + [R.identity(G, tgt(G, d))] * (K - 1)
        else:
            pad, cur = [], src(G, s[i])
            for _, j, k in allc:
                if j == i:
                    pad.append(chunks[i][k])
                    cur = tgt(G, chunks[i][k])
                else:
                    pad.append(R.identity(G, cur))
        dp = R.vcomp_over_terms(G, n, pad)
        if i in pre:
            c0 = pre[i][0]
            W2 = _R()._rc_inner(G, infer(G, c0), c0, dp)
            if W2 is None:
                return None
            W = comp2(G, n, pre[i][1], W2)
        else:
            W = _R()._rc_inner(G, infer(G, s[i]), s[i], dp)
            if W is None:
                return None
        new[i] = (dp, W)
        fss[i] = pad
    Cg, h1 = congruence(G, h, new, True)
    col, D = I._distribute_pairs(G, h1, fss, True)
    if D is None:
        return None
    return col, comp2(G, n, Cg, D)

def _split_factor(G, h, n, order_key):
    """h = H(.., c_i, ..) a composition head of dimension n whose top slots
    i hold the events. Returns (seq, D): seq the sequential composite
    H(c_1, 1, ..) * H(1, c_2, ..) * ... in the order given by order_key on
    the slots, and D : h -> seq, one coherence over H's arity."""
    R = _R()
    if h[0] != 'coh':
        return None
    _, P, B, s = h
    if tdim(B) + 1 != n or ps_dim(P) != n:
        return None
    tops = [i for i, C in enumerate(P) if tdim(C) + 1 == n]
    act = [i for i in tops if _events(G, s[i], n)]
    if len(act) == 1 and len(_events(G, s[act[0]], n)) >= 2:
        return _split_nested(G, h, n, order_key, act[0], tops)
    if len(act) < 2:
        return None
    if any(len(_events(G, s[i], n)) >= 2 for i in act):
        return _split_general(G, h, n, order_key)
    act.sort(key=lambda i: order_key(s[i]))
    rest = [i for i in tops if i not in act]
    idP = list(v(i) for i in range(len(P)))
    H0 = ('coh', P, B, tuple(idP))
    done = set()
    parts = []
    # slots without events stay with the first factor
    for k, i in enumerate(act):
        im = list(idP)
        for j in tops:
            a, b = P[j][2], P[j][3]
            if j == i or (k == 0 and j in rest):
                continue
            face = b if j in done or (j in rest) else a
            im[j] = R.identity(P, face)
            # faces of this slot collapse onto the chosen face
            im[P[j][3][1]] = face
            im[P[j][2][1]] = face
        done.add(i)
        try:
            parts.append(('coh', P, B, tuple(im)))
        except Exception:
            return None
    try:
        seq0 = R.vcomp_over_terms(P, n, parts)
        T = infer(P, H0)
        if infer(P, seq0) != T or not side_ok(P, T, H0, seq0):
            return None
    except (TypeError_, AssertionError, KeyError):
        return None
    D = ('coh', P, arr(T, H0, seq0), s)
    return subst_tm(seq0, s), D

def split_mixed(G, A, t, u, rec):
    """A top-cut factor H(.., z.., c, ..) of t (or u) with its events in one
    top slot and coherence n-cells c in others is split into the sequential
    composite H(z, 1) * H(1, c) or H(1, c) * H(z, 1) (whichever leads to an
    answer), as in split_events."""
    R = _R()
    n = tdim(A) + 1
    for side in (0, 1):
        x = t if side == 0 else u
        fx = R.vfactors(G, x, n)
        for k, f in enumerate(fx):
            if f[0] != 'coh' or ps_dim(f[1]) != n or tdim(f[2]) + 1 != n:
                continue
            tops = [i for i, C in enumerate(f[1]) if tdim(C) + 1 == n]
            if len([i for i in tops if _events(G, f[3][i], n)]) != 1:
                continue
            for ck in ((-1, -1), (10 ** 7, 0)):
                try:
                    r = _split_general(G, f, n, lambda c: (0, 0), ck)
                except (TypeError_, AssertionError, KeyError, ValueError):
                    r = None
                if r is None:
                    continue
                seq, D = r
                sf = R.vfactors(G, seq, n)
                x2 = R.vcomp_over_terms(G, n, fx[:k] + sf + fx[k + 1:])
                Wd = _segments(G, A, x, x2, [fx[:k], [f], fx[k + 1:]], [fx[:k], sf, fx[k + 1:]], rec, {1: D})
                if Wd is None:
                    continue
                if side == 0:
                    rest = rec(G, A, x2, u)
                    if rest is not None:
                        return comp2(G, n, Wd, rest)
                else:
                    import rc_inverse as I
                    rest = rec(G, A, t, x2)
                    Wi = I.inverse(G, Wd) if rest is not None else None
                    if Wi is not None:
                        return comp2(G, n, rest, Wi)
    return None

def unloop(G, A, t, u, rec):
    """A variable y : p -> p with p a variable (a loop): answer the query in
    the context with a fresh p' : type p inserted before y and y : p -> p',
    the terms rebuilt from the images of each head's locally maximal
    variables, and substitute p' := p back. Skipped when the rebuilt query
    is ill-typed there or does not substitute back to the given one."""
    from catt import sub_from
    R = _R()
    used = fv_tm(t) | fv_tm(u)
    for y in sorted(used):
        T = G[y]
        if T == STAR or T[2] != T[3] or T[2][0] != 'v':
            continue
        p = T[2][1]
        sh = tuple(v(i) if i < y else v(i + 1) for i in range(len(G)))
        G2 = list(G[:y]) + [G[p]]
        for i in range(y, len(G)):
            Ti = subst_ty(G[i], sh)
            if i == y:
                Ti = arr(Ti[1], Ti[2], v(y))
            G2.append(Ti)
        G2 = tuple(G2)
        back = tuple(v(i) for i in range(y)) + (v(p),) + tuple(v(i) for i in range(y, len(G)))
        def rw(w):
            if w[0] == 'v':
                return sh[w[1]]
            _, P, B, sg = w
            imgs = {m: rw(sg[m]) for m in maximal_vars(P)}
            sg2 = sub_from(P, G2, imgs)
            return ('coh', P, B, tuple(sg2[i] for i in range(len(P))) if isinstance(sg2, dict) else tuple(sg2))
        try:
            check_ctx(G2)
            t2, u2 = rw(t), rw(u)
            A2 = infer(G2, t2)
            if infer(G2, u2) != A2 or subst_tm(t2, back) != t or subst_tm(u2, back) != u:
                continue
            if R.strict_image(G2, t2) != R.strict_image(G2, u2):
                continue
        except (TypeError_, AssertionError, KeyError, ValueError):
            continue
        w = rec(G2, A2, t2, u2)
        if w is not None:
            return subst_tm(w, back)
    return None

def _remove_leaves(tree, leaves):
    """Remove the leaves at the given paths. Returns (tree', pmap) with
    pmap {old path: new path} for the remaining nodes."""
    pmap = {}
    def go(node, old, new):
        out = []
        for i, child in enumerate(node):
            op = old + (i,)
            if op in leaves:
                continue
            np_ = new + (len(out),)
            pmap[op] = np_
            out.append(go(child, op, np_))
        return tuple(out)
    return go(tree, (), ()), pmap

def drop_units(G, h, n):
    """h = H(.., 1_y, ..) a composition head of dimension n with canonical
    identities in some top slots (also inside top slots that are single
    composition heads themselves): (h', D) with h' the unbiased composite of
    H's pasting context without those leaves, at the remaining arguments,
    and D : h -> h'. None when there is nothing to drop."""
    R = _R()
    if h[0] != 'coh':
        return None
    _, P, B, s = h
    if tdim(B) + 1 != n or ps_dim(P) != n:
        return None
    tops = [i for i, C in enumerate(P) if tdim(C) + 1 == n]
    steps = []
    new = {}
    for i in tops:
        r = drop_units(G, s[i], n)
        if r is not None:
            new[i] = r
    if new:
        Cg, h = congruence(G, h, new, True)
        steps.append(Cg)
        _, P, B, s = h
    units = [i for i in tops if s[i][0] == 'coh' and s[i] == R.identity(G, src(G, s[i]))]
    if units and len(units) < len(tops):
        tree = tree_of(P)
        paths = _paths(tree)
        T2, pmap = _remove_leaves(tree, {paths[i] for i in units})
        P2 = tree_ctx(T2)
        var2 = {p: j for j, p in enumerate(_paths(T2)) if p is not None}
        mx2 = maximal_vars(P2)
        old_of = {j: i for i, pth in enumerate(paths) if pth is not None and pth in pmap for j in [var2[pmap[pth]]]}
        try:
            s2 = sub_from(P2, G, {m: s[old_of[m]] for m in mx2})
            # P -> P2: removed leaves go to identities on their source
            im = {}
            for m in maximal_vars(P):
                if m in units:
                    continue
                im[m] = v(var2[pmap[paths[m]]])
            for m in units:
                a = P[m][2][1]
                pa = paths[a]
                if pa is not None:
                    im_a = v(var2[pmap[pa]])
                else:
                    # an object: the target of the previous sibling, or the parent edge
                    pth = paths[m]
                    j = pth[-1]
                    if j == 0:
                        im_a = v(var2[pmap[pth[:-1]]]) if pth[:-1] else None
                    else:
                        prev = pth[:-1] + (j - 1,)
                        im_a = v(var2[pmap[prev]] - 1) if prev in pmap else None
                    if im_a is None:
                        return None
                im[m] = R.identity(P2, im_a)
            rho = sub_from(P, P2, im)
            lhs = ('coh', P, B, tuple(rho))
            rhs = ucomp(P2)
            T = infer(P2, lhs)
            if infer(P2, rhs) != T or not side_ok(P2, T, lhs, rhs):
                return None
            if subst_tm(lhs, s2) != h:
                return None
            steps.append(('coh', P2, arr(T, lhs, rhs), tuple(s2)))
            h = subst_tm(rhs, s2)
        except (TypeError_, AssertionError, KeyError, ValueError):
            return None
    if not steps:
        return None
    out = steps[0]
    for y in steps[1:]:
        out = comp2(G, n, out, y)
    return h, out

def unit_slots(G, A, t, u, rec):
    """Drop identity top slots of the factors of t and u (drop_units), then
    compare the results by `rec`."""
    return _per_factor(G, A, t, u, rec, lambda f, n: drop_units(G, f, n))

def flatten(G, A, t, u, rec):
    """Distribute every factor of t and u over the vertical composites in
    its (nested) top slots (_flatten), then compare the results by `rec`."""
    return _per_factor(G, A, t, u, rec, lambda f, n: _flatten(G, f, n, rec))

def _flatten(G, h, n, rec):
    """h = H(.., c_i, ..) a composition head of dimension n whose top slots
    (after flattening them in turn) are vertical composites: (seq, D) with
    seq = H(c_1 pieces, 1..) * H(1.., c_2 pieces, ..) * ..., slot after slot,
    every slot padded with identities, and D : h -> seq."""
    R = _R()
    import rc_inverse as I
    if h[0] != 'coh':
        return None
    _, P, B, s = h
    if tdim(B) + 1 != n or ps_dim(P) != n:
        return None
    tops = [i for i, C in enumerate(P) if tdim(C) + 1 == n]
    pieces, pre = {}, {}
    for i in tops:
        r = _flatten(G, s[i], n, rec)
        if r is not None:
            pre[i] = r
            pieces[i] = R.vfactors(G, r[0], n)
        else:
            ps_ = _vpieces(G, s[i], n)
            ok = len(ps_) > 1 and src(G, ps_[0]) == src(G, s[i]) and all(
                tgt(G, x) == src(G, y) for x, y in zip(ps_, ps_[1:])) and tgt(G, ps_[-1]) == tgt(G, s[i])
            pieces[i] = ps_ if ok else [s[i]]
    if not pre and all(len(pieces[i]) <= 1 for i in tops):
        return None
    order = [(i, k) for i in tops for k in range(len(pieces[i]))]
    K = len(order)
    if K < 2:
        return None
    fss, new = {}, {}
    for i in tops:
        pad, cur = [], src(G, s[i])
        for j, k in order:
            if j == i:
                pad.append(pieces[i][k])
                cur = tgt(G, pieces[i][k])
            else:
                pad.append(R.identity(G, cur))
        dp = R.vcomp_over_terms(G, n, pad)
        base = pre[i][0] if i in pre else s[i]
        W2 = None if base == dp else _R()._rc_inner(G, infer(G, base), base, dp)
        if base != dp and W2 is None:
            return None
        W = pre[i][1] if i in pre else None
        W = W2 if W is None else (W if W2 is None else comp2(G, n, W, W2))
        if W is None:
            W = R.identity(G, s[i])
        new[i] = (dp, W)
        fss[i] = pad
    Cg, h1 = congruence(G, h, new, True)
    col, D = I._distribute_pairs(G, h1, fss, True)
    if D is None:
        return None
    return col, comp2(G, n, Cg, D)

def _vpieces(G, w, n):
    """The literal vertical pieces of w: the arguments of nested column
    heads (pasting context a column of n-cells)."""
    R = _R()
    if w[0] == 'coh' and ps_dim(w[1]) == n and tdim(w[2]) + 1 == n and (R._is_column(w[1], n) or 0) >= 2:
        out = []
        for i, C in enumerate(w[1]):
            if tdim(C) + 1 == n:
                out += _vpieces(G, w[3][i], n)
        try:
            if src(G, out[0]) == src(G, w) and tgt(G, out[-1]) == tgt(G, w) and all(
                    tgt(G, x) == src(G, y) for x, y in zip(out, out[1:])):
                return out
        except (TypeError_, KeyError):
            pass
    return [w]

def _per_factor(G, A, t, u, rec, fn):
    """Rewrite each top-cut factor f of t and u by fn(f, n) = (f', D : f -> f')
    or None, then compare the rewritten terms by `rec`."""
    R = _R()
    import rc_inverse as I
    n = tdim(A) + 1
    sides = []
    for x in (t, u):
        fx = R.vfactors(G, x, n)
        nf, given = [], {}
        for k, f in enumerate(fx):
            try:
                r = fn(f, n)
            except (TypeError_, AssertionError, KeyError, ValueError):
                r = None
            if r is None:
                nf.append(f)
            else:
                nf.append(r[0]); given[k] = r[1]
        if not given:
            sides.append((x, None))
            continue
        x2 = R.vcomp_over_terms(G, n, nf)
        W = _segments(G, A, x, x2, [[f] for f in fx], [[f] for f in nf], rec, given)
        if W is None:
            return None
        sides.append((x2, W))
    (t2, Wt), (u2, Wu) = sides
    if Wt is None and Wu is None:
        return None
    mid = rec(G, A, t2, u2)
    if mid is None:
        return None
    out = mid
    if Wt is not None:
        out = comp2(G, n, Wt, out)
    if Wu is not None:
        Wi = I.inverse(G, Wu)
        if Wi is None:
            return None
        out = comp2(G, n, out, Wi)
    return out

def split_events(G, A, t, u, rec):
    """A top-cut factor of t (or u) carrying several events in different top
    slots of its head is split into the sequential composite, in the order
    in which those events occur on the other side."""
    R = _R()
    n = tdim(A) + 1
    for side in (0, 1):
        x, y = (t, u) if side == 0 else (u, t)
        fx, fy = R.vfactors(G, x, n), R.vfactors(G, y, n)
        pos = {}
        for k, f in enumerate(fy):
            for z in _events(G, f, n):
                pos.setdefault(z, k)
        key = lambda c: min((pos.get(z, 10 ** 6), z) for z in _events(G, c, n))
        for k, f in enumerate(fx):
            if len(_events(G, f, n)) < 2:
                continue
            r = _split_factor(G, f, n, key)
            if r is None:
                continue
            seq, D = r
            new = fx[:k] + R.vfactors(G, seq, n) + fx[k + 1:]
            x2 = R.vcomp_over_terms(G, n, new)
            Wd = _segments(G, A, x, x2, [fx[:k], [f], fx[k + 1:]], [fx[:k], R.vfactors(G, seq, n), fx[k + 1:]], rec, {1: D})
            if Wd is None:
                continue
            if side == 0:
                rest = rec(G, A, x2, u)
                if rest is None:
                    return None
                return comp2(G, n, Wd, rest)
            else:
                rest = rec(G, A, t, x2)
                if rest is None:
                    return None
                import rc_inverse as I
                Wi = I.inverse(G, Wd)
                if Wi is None:
                    return None
                return comp2(G, n, rest, Wi)
    return None

def _replace(t, a, x):
    if t == a:
        return x
    if t[0] == 'v':
        return t
    return ('coh', t[1], t[2], tuple(_replace(y, a, x) for y in t[3]))

def _replace_ty(A, a, x):
    if A == STAR:
        return A
    return arr(_replace_ty(A[1], a, x), _replace(A[2], a, x), _replace(A[3], a, x))

def _marker_ctx(G, z):
    """Single-event form of _marker_ctx_multi: (G', x, z', fwd, back)."""
    r = _marker_ctx_multi(G, [z])
    if r is None:
        return None
    G2, xs, zm, fwd, back = r
    return G2, xs[z], zm[z], fwd, back

def _marker_ctx_multi(G, zs):
    """For events z : a_z -> b_z, the context where squares along all of
    them are taken: G itself with x_z = a_z for a variable source, and a
    marker pair (X_z : type a_z, Z_z : X_z -> b_z) appended for each
    composite source (r9 Response 3). Returns (G', {z: x_z}, {z: z'}, fwd,
    back): fwd replaces each composite a_z by X_z and z by Z_z (None if
    the result is ill-typed or does not substitute back), back undoes it."""
    xs, zm = {}, {}
    G2 = list(G)
    sg = [v(i) for i in range(len(G))]
    bsub = [v(i) for i in range(len(G))]
    reps = []
    for z in zs:
        a, b = G[z][2], G[z][3]
        if a[0] == 'v':
            xs[z], zm[z] = a[1], z
            continue
        X, Zv = len(G2), len(G2) + 1
        try:
            Ta = infer(G, a)
        except (TypeError_, AssertionError, KeyError):
            return None
        G2 += [Ta, arr(Ta, v(X), b)]
        xs[z], zm[z] = X, Zv
        sg[z] = v(Zv)
        bsub += [a, v(z)]
        reps.append((a, v(X)))
    G2 = tuple(G2)
    sg, bsub = tuple(sg), tuple(bsub)
    try:
        check_ctx(G2)
    except (TypeError_, AssertionError, KeyError):
        return None
    if not reps:
        ident = lambda w: w
        return G, xs, zm, ident, ident
    def back(w):
        return subst_tm(w, bsub)
    def fwd(w):
        w2 = subst_tm(w, sg)
        for a, X in reps:
            w2 = _replace(w2, a, X)
        try:
            infer(G2, w2)
        except (TypeError_, AssertionError, KeyError):
            return None
        return w2 if back(w2) == w else None
    return G2, xs, zm, fwd, back

def _rebuilder(G, Gm, ren):
    """w over G -> w over Gm with the variables in ren renamed and every
    head's lower arguments re-derived from the images of its locally
    maximal variables (so faces follow the new types); None if ill-typed."""
    from catt import sub_from
    memo = {}
    def rw(w):
        if w[0] == 'v':
            return ren.get(w[1], w)
        k = id(w)
        if k in memo and memo[k][0] is w:
            return memo[k][1]
        _, P, B, sg = w
        imgs = {m: rw(sg[m]) for m in maximal_vars(P)}
        r = ('coh', P, B, tuple(sub_from(P, Gm, imgs)))
        memo[k] = (w, r)
        return r
    def go(w):
        try:
            r = rw(w)
            infer(Gm, r)
            return r
        except (TypeError_, AssertionError, KeyError, ValueError):
            return None
    return go

def markerize(G, A, t, u, rec):
    """An event z : a -> b whose source a is a composite term: rewrite the
    query over G + (X : type a) + (Z : X -> b), replacing a by the marker X
    and z by Z (r9 Response 3: markers have the actual raw type of the
    faces), answer it there, and substitute back."""
    n = tdim(A) + 1
    zs = sorted({z for z in fv_tm(t) | fv_tm(u) if G[z] != STAR and tdim(G[z]) + 1 == n and G[z][2][0] == 'coh'})
    for z in zs:
        a, b = G[z][2], G[z][3]
        X = len(G)
        Zv = X + 1
        Ta = infer(G, a)
        G2 = G + (Ta, arr(Ta, v(X), b))
        rz = lambda w: _replace(subst_tm(w, tuple(v(i) if i != z else v(Zv) for i in range(len(G)))), a, v(X))
        A2 = _replace_ty(subst_ty(A, tuple(v(i) if i != z else v(Zv) for i in range(len(G)))), a, v(X))
        t2, u2 = rz(t), rz(u)
        back = tuple(v(i) for i in range(len(G))) + (a, v(z))
        try:
            check_ctx(G2)
            if infer(G2, t2) != A2 or infer(G2, u2) != A2:
                continue
            if subst_tm(t2, back) != t or subst_tm(u2, back) != u:
                continue
        except (TypeError_, AssertionError, KeyError):
            continue
        w = rec(G2, A2, t2, u2)
        if w is not None:
            return subst_tm(w, back)
    return None

def swap_first(G, A, t, u, rec):
    """Sorting step (r9 Response 3): if the first event of u is z and t has
    an event factor f immediately followed by the factor g of z : y -> Z,
    with y a variable occurring in f, rewrite t so that z comes first:
    f g -> f (tau f)^ Q -> (sigma f)^ f+ Q (naturality square of f along z
    at y), where Q connects the lift's target to g's (rank n-1), and g is
    compared with (tau f)^ Q by `rec`. Then compare the result with u."""
    R = _R()
    import rc_nat as N
    n = tdim(A) + 1
    ft, fu = R.vfactors(G, t, n), R.vfactors(G, u, n)
    eu = [_events(G, f, n) for f in fu]
    first_u = next((e for e in eu if e), None)
    if not first_u or len(first_u) != 1:
        return None
    z = first_u[0]
    ks = [k for k, f in enumerate(ft) if z in _events(G, f, n)]
    if len(ks) != 1 or ks[0] == 0:
        return None
    k = ks[0]
    # f: the last event factor before g, with the coherence factors after it
    k0 = max((j for j in range(k) if _events(G, ft[j], n)), default=None)
    if k0 is None:
        return None
    f_list, g = ft[k0:k], ft[k]
    f = R.vcomp_over_terms(G, n, f_list) if len(f_list) > 1 else f_list[0]
    if z in _events(G, f, n):
        return None
    Z = G[z][3]
    mk = _marker_ctx(G, z)
    if mk is None:
        return None
    Gm, x, zm, fwd, back = mk
    fm = fwd(f)
    if fm is None or x not in fv_tm(fm):
        return None
    try:
        sq, sa, sb = (back(w) for w in N.square(Gm, {x}, {x: Z}, {x: v(zm)}, fm, rec))
        Lg = back(N.nat_in(Gm, frozenset({x}), {x: Z}, {x: v(zm)}, tgt(Gm, fm), rec))
    except (N.NoFiller, TypeError_, AssertionError, KeyError, ValueError):
        return None
    fl = R.vfactors(G, Lg, n)
    pre, rest = ft[:k0], ft[k + 1:]
    steps = []
    if tgt(G, Lg) != tgt(G, g):
        Q = rec(G, infer(G, tgt(G, Lg)), tgt(G, Lg), tgt(G, g))
        if Q is None:
            return None
        mid = fl + [Q]
    else:
        Q, mid = None, fl
    t1 = _vc_or_id(G, n, pre + f_list + mid + rest, A[2])
    if t1 != t:
        W1 = _segments(G, A, t, t1, [pre + f_list, [g], rest], [pre + f_list, mid, rest], rec)
        if W1 is None:
            return None
        steps.append(W1)
    # the square, whiskered
    W = sq
    post = ([Q] if Q is not None else []) + rest
    if post:
        W = comp2(G, n - 1, W, R.vcomp_over_terms(G, n, post))
    if pre:
        W = comp2(G, n - 1, R.vcomp_over_terms(G, n, pre), W)
    if src(G, W) != t1:
        x = rec(G, A, t1, src(G, W))
        if x is None:
            return None
        steps.append(x)
    steps.append(W)
    x = rec(G, A, tgt(G, W), u)
    if x is None:
        return None
    steps.append(x)
    out = steps[0]
    for y_ in steps[1:]:
        out = comp2(G, n, out, y_)
    return out

def _flipped(G, A, t, u, rec, step):
    """step applied to (u, t), inverted (rc_inverse.inverse, re-typed)."""
    import rc_inverse as I
    w = step(G, A, u, t, rec)
    if w is None:
        return None
    wi = I.inverse(G, w)
    if wi is None or infer(G, wi) != arr(A, t, u):
        return None
    return wi

def C1_D1_differ(a, b):
    return a != b

DESCENT = [False, 40]

def _descent(G, A, t, u, rec):
    """r9 Response 15, single piece (tools/rc_descent.py); off by default,
    and only for contexts of at most DESCENT[1] variables."""
    if not DESCENT[0] or len(G) > DESCENT[1]:
        return None
    import rc_descent
    return rc_descent.piece(G, A, t, u, rec)

def change_of_writing(G, A, t, u, rec):
    """Change of writing for an event factor (r9 Response 3). t = C1 E C2 and
    u = D1 E' D2 along the top cut, where C1, D1 contain no n-variable and
    E, E' contain the same n-variables z : a_z -> b_z (composite sources
    through marker contexts, _marker_ctx_multi), all lifted at once. With J : src E' -> src E (rank n-1), the naturality square
    of J along z at a (rc_nat.square) gives J (src E)^ -> (src E')^ J+, so
      t -> C1 J^-1 J (src E)^ C2 -> C1 J^-1 (src E')^ J+ C2 -> u,
    the remaining comparisons (E with (src E)^, the old blocks, E' with
    (src E')^) by `rec`."""
    R = _R()
    import rc_nat as N, rc_inverse as I
    n = tdim(A) + 1
    ft, fu = R.vfactors(G, t, n), R.vfactors(G, u, n)
    et = [k for k, f in enumerate(ft) if _events(G, f, n)]
    eu = [k for k, f in enumerate(fu) if _events(G, f, n)]
    if not et or not eu:
        return None
    i, j = et[0], eu[0]
    E, E2 = ft[i], fu[j]
    zs = _events(G, E, n)
    if sorted(zs) != sorted(_events(G, E2, n)) or not zs:
        return None
    mk = _marker_ctx_multi(G, zs)
    if mk is None:
        return None
    Gm, xs_, zms, fwd, back = mk
    rebuild = _rebuilder(G, Gm, {z: v(zms[z]) for z in zs})
    Ym = frozenset(xs_.values())
    pmap = {xs_[z]: G[z][3] for z in zs}
    umap = {xs_[z]: v(zms[z]) for z in zs}
    sE, sE2 = src(G, E), src(G, E2)
    if sE == sE2:
        # same writing at the event: no change of writing needed
        if i > 0 or j > 0:
            return _segments(G, A, t, u, [ft[:i], ft[i:]], [fu[:j], fu[j:]], rec)
        C2, D2 = ft[1:], fu[1:]
        if tgt(G, E) == tgt(G, E2) and (C2 or D2):
            return _segments(G, A, t, u, [[E], C2], [[E2], D2], rec)
        if not any(_events(G, f, n) for f in C2 + D2):
            return None            # a single event against a single event: other steps
        if tgt(G, E) == tgt(G, E2):
            return _segments(G, A, t, u, [[E], C2], [[E2], D2], rec)
        Q = rec(G, infer(G, tgt(G, E)), tgt(G, E), tgt(G, E2))
        if Q is None:
            return None
        Qi = I.inverse(G, Q)
        cq = I.cancel(G, Q, rec)
        ins = I.inverse(G, cq) if cq is not None else None
        if Qi is None or ins is None:
            return None
        t2 = R.vcomp_over_terms(G, n, [E, Q, Qi] + C2)
        W0 = _segments(G, A, t, t2, [[E], [], C2], [[E], [Q, Qi], C2], rec, {1: ins})
        if W0 is None:
            return None
        W1 = _segments(G, A, t2, u, [[E, Q], [Qi] + C2], [[E2], D2], rec)
        if W1 is None:
            return None
        return comp2(G, n, W0, W1)
    # the sources over the markers: rebuild the event factors with z := Z_z
    # (lower arguments re-derived from the types), then take their sources
    Em, E2m = rebuild(E), rebuild(E2)
    if Em is None or E2m is None:
        return None
    sEm, sE2m = src(Gm, Em), src(Gm, E2m)
    if back(sEm) != sE or back(sE2m) != sE2:
        return None
    Jm = rec(Gm, infer(Gm, sE2m), sE2m, sEm)       # J : src E' -> src E
    if Jm is None:
        return None
    # J is taken as the inverse of J^-1, so that J^-1 J is a cancellation
    Jim = I.inverse(Gm, Jm)
    Jm2 = I.inverse(Gm, Jim) if Jim is not None else None
    if Jm2 is None or infer(Gm, Jm2) != infer(Gm, Jm):
        return None
    Jm, Ji, Jp = Jm2, back(Jim), back(Jm2)
    cj = I.cancel(G, Ji, rec)
    ins = I.inverse(G, cj) if cj is not None else None
    if ins is None:
        return None
    try:
        sq, sa, sb = (back(w) for w in N.square(Gm, Ym, pmap, umap, Jm, rec))
    except (N.NoFiller, TypeError_, AssertionError, KeyError, ValueError):
        return None
    # sa = J *_{n-2}... (src E)^ ; sb = (src E')^ * J+ ; with J+ = J[x := b]
    m = n - 1          # composition of n-cells along m-1 = n-2? no: vertical along n-1
    C1, C2 = ft[:i], ft[i + 1:]
    D1, D2 = fu[:j], fu[j + 1:]
    sa_f = R.vfactors(G, sa, n)
    sb_f = R.vfactors(G, sb, n)
    # pieces as factor lists
    C2o = C2
    Jf = R.vfactors(G, Jp, n)
    if sa_f[:len(Jf)] != Jf:
        return None
    liftf = sa_f[len(Jf):]
    if tgt(G, sa) != tgt(G, E):
        # the lift of src E ends elsewhere than E: a connector (rank n-1)
        Q0 = rec(G, infer(G, tgt(G, sa)), tgt(G, sa), tgt(G, E))
        if Q0 is None:
            return None
        C2 = [Q0] + C2
        liftf = liftf + [Q0]
    lhs = C1 + [Ji] + sa_f + C2          # after inserting J^-1 J
    S = A[2]
    steps = []
    # t -> C1 J^-1 J (src E)^ C2 : insert J^-1 J, compare E with the lift
    L = _vc_or_id(G, n, lhs, S)
    x1 = _segments(G, A, t, L, [C1, [], [E], C2o], [C1, [Ji] + Jf, liftf, C2o], rec, {1: ins})
    if x1 is None:
        return None
    steps.append(x1)
    # whisker the square
    W = sq
    pre, post = C1 + [Ji], C2
    if post:
        W = comp2(G, n - 1, W, R.vcomp_over_terms(G, n, post))
    if pre:
        W = comp2(G, n - 1, R.vcomp_over_terms(G, n, pre), W)
    if src(G, W) != L:
        x2 = rec(G, A, L, src(G, W))
        if x2 is None:
            return None
        steps.append(x2)
    steps.append(W)
    tw = tgt(G, W)
    fw = R.vfactors(G, tw, n)
    try:
        lift2 = back(N.nat_in(Gm, Ym, pmap, umap, sE2m, rec))
    except (N.NoFiller, TypeError_, AssertionError, KeyError, ValueError):
        return None
    fl = R.vfactors(G, lift2, n)
    # the lift sits after C1 J^-1, possibly after further old factors of
    # the square's target (the square's own whiskers): find it
    k0 = len(C1) + 1
    pos = next((s_ for s_ in range(k0, len(fw) - len(fl) + 1) if fw[s_:s_ + len(fl)] == fl), None)
    if pos is None:
        return None
    left, rest = fw[:pos], fw[pos + len(fl):]
    Q = None
    if tgt(G, lift2) != tgt(G, E2):
        Q = rec(G, infer(G, tgt(G, lift2)), tgt(G, lift2), tgt(G, E2))
        if Q is None:
            return None
        Qi = I.inverse(G, Q)
        cq = I.cancel(G, Q, rec)
        ins = I.inverse(G, cq) if cq is not None else None
        if Qi is None or ins is None:
            return None
        tw2 = _vc_or_id(G, n, left + fl + [Q, Qi] + rest, A[2])
        x2b = _segments(G, A, tw, tw2, [left + fl, [], rest], [left + fl, [Q, Qi], rest], rec, {1: ins})
        if x2b is None:
            return None
        steps.append(x2b)
        tw, mid, rest = tw2, fl + [Q], [Qi] + rest
    else:
        mid = fl
    x3 = _segments(G, A, tw, u, [left, mid, rest], [D1, [E2], D2], rec)
    if x3 is None:
        return None
    steps.append(x3)
    out = steps[0]
    for y in steps[1:]:
        out = comp2(G, n, out, y)
    return out

CALLS = [0]          # reset by rc_oracle.rc for each top-level query
LIMIT = 400

BLOCKED = [0]        # cycle-guard refusals (a failure under one is not final)
INPROG = set()       # queries currently being answered (cycle guard)

def heur(G, A, t, u, rec):
    key = (G, t, u)
    if key in INPROG:
        BLOCKED[0] += 1
        return None
    INPROG.add(key)
    try:
        return _heur(G, A, t, u, rec)
    finally:
        INPROG.discard(key)

def _heur(G, A, t, u, rec):
    R = _R()
    CALLS[0] += 1
    if CALLS[0] > LIMIT:
        raise R.NotCovered('rc_heur: call budget exhausted')
    n = tdim(A) + 1
    try:
        t2, Ct = slot_norm(G, t, True, rec)
    except (TypeError_, AssertionError, KeyError, ValueError):
        t2, Ct = t, None
    try:
        u2, Cu = slot_norm(G, u, False, rec)
    except (TypeError_, AssertionError, KeyError, ValueError):
        u2, Cu = u, None
    X = None
    if t2 != u2:
        if (t2, u2) != (t, u):
            X = rec(G, A, t2, u2)
        else:
            import rc_nat
            idt = R.identity(G, A[2]) if A[2] == A[3] else None
            steps = [
                lambda: rebracket(G, A, t, u),
                lambda: cancel_loop(G, A, t, True, rec) if idt is not None and u == idt else None,
                lambda: cancel_loop(G, A, u, False, rec) if idt is not None and t == idt else None,
                lambda: interchange(G, A, t, u, rec),
                lambda: _descent(G, A, t, u, rec),
                lambda: change_of_writing(G, A, t, u, rec),
                lambda: swap_first(G, A, t, u, rec),
                lambda: _flipped(G, A, t, u, rec, swap_first),
                lambda: split_events(G, A, t, u, rec),
                lambda: split_mixed(G, A, t, u, rec),
                lambda: unit_slots(G, A, t, u, rec),
                lambda: flatten(G, A, t, u, rec),
                lambda: unloop(G, A, t, u, rec),
                lambda: markerize(G, A, t, u, rec),
                lambda: rc_nat.sweep_rc(G, A, t, u, rec),
                lambda: via_abstraction(G, A, t, u, rec),
            ]
            for step in steps:
                try:
                    X = step()
                except (TypeError_, AssertionError, KeyError, ValueError, StopIteration):
                    X = None        # a step that breaks fails alone
                if X is not None:
                    break
        if X is None:
            return None
    cells = [c for c in (Ct, X, Cu) if c is not None]
    if not cells:
        return None
    out = cells[0]
    for c in cells[1:]:
        out = comp2(G, n, out, c)
    return out
