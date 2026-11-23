"""Inverse data for raw tracks without top-rank variables (r9 Response 4,
"Comparisons used in cancellation"). Untrusted oracle code: every result
is type-checked by catt.infer.

  inverse(G, t)  -> t' : tgt t -> src t, or None
  cancel(G, t, rc) -> (t *_{n-1} t' -> 1_{src t}), via rc, or None
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from catt import *

def _R():
    import rc_oracle
    return rc_oracle

def _top_vars(P, n):
    return [i for i, B in enumerate(P) if tdim(B) + 1 == n]

def inverse(G, t):
    """Structural inverse of an n-track t (n = dimension of t) in which no
    n-variable occurs:
      * a coherence over an arity of height < n: reverse its type;
      * a coherence over an arity of height n: invert the top arguments and
        swap the (n-1)-faces of each top variable of the arity (a column
        reverses its order). Requires the top variables to have pairwise
        distinct (n-1)-faces, or the arity to be a column."""
    if t[0] != 'coh':
        return None
    _, P, B, s = t
    n = tdim(B) + 1
    p = ps_dim(P)
    if p < n:
        B2 = arr(B[1], B[3], B[2])
        if not side_ok(P, B2[1], B2[2], B2[3]):
            return None
        return ('coh', P, B2, s)
    tops = _top_vars(P, n)
    R = _R()
    if R._is_column(P, n) and len(tops) > 1:
        fs = [inverse(G, s[i]) for i in tops]
        if any(f is None for f in fs):
            return None
        return R.vcomp_over_terms(G, n, list(reversed(fs)))
    faces = []
    for i in tops:
        a, b = P[i][2][1], P[i][3][1]
        faces += [a, b]
    if len(set(faces)) != len(faces):
        return None
    s2 = list(s)
    for i in tops:
        a, b = P[i][2][1], P[i][3][1]
        g = inverse(G, s[i])
        if g is None:
            return None
        s2[a], s2[b], s2[i] = s[b], s[a], g
    w = ('coh', P, B, tuple(s2))
    try:
        T = infer(G, w)
    except Exception:
        return None
    S = infer(G, t)
    if T[2] != S[3] or T[3] != S[2]:
        return None
    return w

def _distribute_pairs(G, h, fss, forward):
    """rc_heur.distribute with the factor lists of the top slots given
    explicitly (no flattening): h = H(.., c_i, ..) with c_i the composite of
    fss[i]; returns D : h -> H(f_1) * ... * H(f_k) (forward) or back."""
    import rc_heur as Hh
    R = _R()
    _, P, B, s = h
    N = tdim(B) + 1
    tops = sorted(fss)
    k = len(fss[tops[0]])
    tree = tree_of(P)
    paths = Hh._paths(tree)
    parents = [paths[i][:-1] for i in tops]
    if len(set(parents)) != len(parents):
        return None, None
    Tk, pmap, smap = Hh._split_leaves(tree, {paths[i] for i in tops}, k)
    Pk = tree_ctx(Tk)
    var_at = {p: j for j, p in enumerate(Hh._paths(Tk)) if p is not None}
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
    im = dict(other)
    for i in tops:
        im[i] = R.vcomp_over_terms(Pk, N, [v(x) for x in sib[i]])
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
    return subst_tm(rhs, sk), D

def _generic_cancel(P, B, s):
    """For an invertible coherence c = coh_P(B)[s] (arity height < dim):
    the coherence c * c^{-1} -> 1_{src c}."""
    R = _R()
    n = tdim(B) + 1
    idP = tuple(v(i) for i in range(len(P)))
    c0 = ('coh', P, B, idP)
    i0 = ('coh', P, arr(B[1], B[3], B[2]), idP)
    loop = comp2(P, n - 1, c0, i0)
    one = R.identity(P, B[2])
    T = infer(P, loop)
    if not side_ok(P, T, loop, one):
        return None
    return ('coh', P, arr(T, loop, one), s)

def _cancel_list(G, fs, rec):
    """fs a list of single factors f_1..f_k; a comparison
    f_1 * ... * f_k * f_k^{-1} * ... * f_1^{-1} -> 1 (right nested)."""
    R = _R()
    n = tdim(infer(G, fs[0])) + 1
    if len(fs) == 1:
        return cancel1(G, fs[0], rec)
    f, rest = fs[0], fs[1:]
    fi = inverse(G, f)
    inv_rest = [inverse(G, x) for x in reversed(rest)]
    if fi is None or any(x is None for x in inv_rest):
        return None
    full = R.vcomp_over_terms(G, n, fs + inv_rest + [fi])
    mid = R.vcomp_over_terms(G, n, rest + inv_rest)
    grouped = R.vcomp_over_terms(G, n, [f, mid, fi])
    Wm = _cancel_list(G, rest, rec)
    if Wm is None:
        return None
    one = R.identity(G, src(G, rest[0]))
    W = comp2(G, n - 1, comp2(G, n - 1, f, Wm), fi)
    after = R.vcomp_over_terms(G, n, [f, one, fi])
    A = infer(G, full)
    steps = []
    if full != grouped:
        x = rec(G, A, full, src(G, W))
        if x is None:
            return None
        steps.append(x)
    steps.append(W)
    pair = comp2(G, n - 1, f, fi)
    x = rec(G, A, tgt(G, W), pair)
    if x is None:
        return None
    steps.append(x)
    c = cancel1(G, f, rec)
    if c is None:
        return None
    steps.append(c)
    out = steps[0]
    for y in steps[1:]:
        out = comp2(G, n, out, y)
    return out

def cancel1(G, f, rec):
    """f * f^{-1} -> 1_{src f} for a single factor f (not a column)."""
    import rc_heur as Hh
    R = _R()
    if f[0] != 'coh':
        return None
    _, P, B, s = f
    n = tdim(B) + 1
    if ps_dim(P) < n:
        return _generic_cancel(P, B, s)
    if R._is_column(P, n):
        return _cancel_list(G, R.vfactors(G, f, n), rec)
    fi = inverse(G, f)
    if fi is None:
        return None
    tops = _top_vars(P, n)
    fss = {}
    s2 = list(s)
    for i in tops:
        g = s[i]
        gi = inverse(G, g)
        if gi is None:
            return None
        fss[i] = [g, gi]
        b = P[i][3][1]
        s2[b] = s[P[i][2][1]]
        s2[i] = comp2(G, n - 1, g, gi)
    h = ('coh', P, B, tuple(s2))
    col, D = _distribute_pairs(G, h, fss, False)     # D : col -> h
    if D is None:
        return None
    loop = comp2(G, n - 1, f, fi)
    A = infer(G, loop)
    steps = []
    if col != loop:
        x = rec(G, A, loop, col)
        if x is None:
            return None
        steps.append(x)
    steps.append(D)
    new = {}
    for i in tops:
        g = s[i]
        Wg = cancel(G, g, rec)
        if Wg is None:
            return None
        new[i] = (R.identity(G, src(G, g)), Wg)
    Cg, h1 = Hh.congruence(G, h, new, True)
    steps.append(Cg)
    one = R.identity(G, A[2])
    if h1 != one:
        try:
            x = unit_head(G, h1)
        except (TypeError_, AssertionError, KeyError, ValueError):
            x = None
        if x is None:
            x = rec(G, A, h1, one)
        if x is None:
            return None
        steps.append(x)
    out = steps[0]
    for y in steps[1:]:
        out = comp2(G, n, out, y)
    return out

def unit_head(G, h):
    """h = H(1, ..., 1): a composition head of dimension n whose top
    arguments are all identities. The unitor h -> 1_{src h}, one coherence
    over the source boundary of H's arity."""
    R = _R()
    if h[0] != 'coh':
        return None
    _, P, B, s = h
    n = tdim(B) + 1
    if ps_dim(P) != n:
        return None
    tops = _top_vars(P, n)
    for i in tops:
        if s[i] != R.identity(G, s[P[i][2][1]]):
            return None
    S = ps_boundary_vars(P, n - 1, '-')
    lo, li = restrict(P, S)
    pos = {x[1]: j for j, x in enumerate(li)}
    im = [None] * len(P)
    for i in range(len(P)):
        if i in pos:
            im[i] = v(pos[i])
    for i in tops:
        a, b = P[i][2][1], P[i][3][1]
        im[b] = v(pos[a])
    for i in tops:
        im[i] = R.identity(lo, im[P[i][2][1]])
    if any(x is None for x in im):
        return None
    H0 = ('coh', P, B, tuple(im))
    T = infer(lo, H0)
    one = R.identity(lo, T[2])
    if not side_ok(lo, T, H0, one):
        return None
    sl = tuple(s[x[1]] for x in li)
    return ('coh', lo, arr(T, H0, one), sl)

def cancel(G, t, rc):
    """A comparison t *_{n-1} t^{-1} -> 1_{src t}, t^{-1} = inverse(G, t)."""
    R = _R()
    n = tdim(infer(G, t)) + 1
    fs = R.vfactors(G, t, n)
    if len(fs) == 1:
        return cancel1(G, t, rc)
    W = _cancel_list(G, fs, rc)
    ti = inverse(G, t)
    if W is None or ti is None:
        return None
    loop = comp2(G, n - 1, t, ti)
    if src(G, W) == loop:
        return W
    x = rc(G, infer(G, loop), loop, src(G, W))
    if x is None:
        return None
    return comp2(G, n, x, W)
