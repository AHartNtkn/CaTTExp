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
        Tc = R._abstract(G, s[i], N, Ck, ctops, [0])
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

CALLS = [0]          # reset by rc_oracle.rc for each top-level query
LIMIT = 400

def heur(G, A, t, u, rec):
    R = _R()
    CALLS[0] += 1
    if CALLS[0] > LIMIT:
        raise R.NotCovered('rc_heur: call budget exhausted')
    n = tdim(A) + 1
    t2, Ct = slot_norm(G, t, True, rec)
    u2, Cu = slot_norm(G, u, False, rec)
    X = None
    if t2 != u2:
        if (t2, u2) != (t, u):
            X = rec(G, A, t2, u2)
        else:
            X = rebracket(G, A, t, u)
            if X is None and A[2] == A[3]:
                idt = R.identity(G, A[2])
                if u == idt:
                    X = cancel_loop(G, A, t, True, rec)
                elif t == idt:
                    X = cancel_loop(G, A, u, False, rec)
            if X is None:
                X = interchange(G, A, t, u, rec)
            if X is None:
                import rc_nat
                X = rc_nat.sweep_rc(G, A, t, u, rec)
            if X is None:
                X = via_abstraction(G, A, t, u, rec)
        if X is None:
            return None
    cells = [c for c in (Ct, X, Cu) if c is not None]
    if not cells:
        return None
    out = cells[0]
    for c in cells[1:]:
        out = comp2(G, n, out, c)
    return out
