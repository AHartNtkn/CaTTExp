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

def distribute(G, t, forward):
    """If t = H(..., c, ...) with c at the only N-dimensional position of H's
    pasting context and c a composite of k >= 2 factors along N-1, return
    (H(f_1) * ... * H(f_k), D) with D : t -> that (forward) or back. One
    coherence over P^k, the pasting context of H with that leaf replaced by k
    sibling leaves."""
    R = _R()
    if t[0] != 'coh':
        return t, None
    _, P, B, s = t
    N = tdim(B) + 1
    tops = [i for i, C in enumerate(P) if tdim(C) + 1 == N]
    if ps_dim(P) != N or len(tops) != 1:
        return t, None
    i = tops[0]
    fs = R.vfactors(G, s[i], N)
    k = len(fs)
    if k < 2:
        return t, None
    tree = tree_of(P)
    paths = _paths(tree)
    pth = paths[i]
    parent, i0 = pth[:-1], pth[-1]
    Tk = _replace_leaf(tree, pth, k)
    Pk = tree_ctx(Tk)
    pk_paths = _paths(Tk)
    var_at = {p: j for j, p in enumerate(pk_paths) if p is not None}
    sib = [var_at[parent + (i0 + j,)] for j in range(k)]
    mx = maximal_vars(P)
    def iota(j):
        im = {}
        for m in mx:
            im[m] = v(sib[j]) if m == i else v(var_at[_shift_path(paths[m], parent, i0, k)])
        return sub_from(P, Pk, im)
    Hs = [('coh', P, B, iota(j)) for j in range(k)]
    rhs = R.vcomp_over_terms(Pk, N, Hs)
    # the slot argument, with its own bracketing, over Pk
    Ck, ctops = R.column(N, k)
    Tc = R._abstract(G, s[i], N, Ck, ctops, [0])
    to_pk = sub_from(Ck, Pk, {ctops[j]: v(sib[j]) for j in range(k)})
    im = {m: (subst_tm(Tc, to_pk) if m == i else v(var_at[_shift_path(paths[m], parent, i0, k)])) for m in mx}
    lhs = ('coh', P, B, sub_from(P, Pk, im))
    # instantiate Pk in G
    gim = {}
    for m in mx:
        if m == i:
            for j in range(k):
                gim[sib[j]] = fs[j]
        else:
            gim[var_at[_shift_path(paths[m], parent, i0, k)]] = s[m]
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

# ---------------------------------------------------------------- driver

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
