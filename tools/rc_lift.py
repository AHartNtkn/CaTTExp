"""
Word lifting (r9 Response 2): lift a strict word at prescribed raw poles,
given comparisons of lower rank. Part of the descent (notes/rc-generator.md
§4, step 2). Untrusted; every term built is type-checked by catt.infer.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from catt import *
import steiner as St

class LiftFailure(Exception):
    pass

def term_dim(G, X):
    return tdim(infer(G, X)) + 1

def pole(G, X, j, sign):
    """The j-dimensional source/target of a term X (X itself at its own rank)."""
    while term_dim(G, X) > j:
        A = infer(G, X)
        X = A[2] if sign == '-' else A[3]
    return X

def adjust(G, X, j, new_src, new_tgt, cmp):
    """Change the j-poles of X (j < dim X) to new_src / new_tgt (None: keep),
    by whiskering comparisons at cut j (Response 2)."""
    if new_src is not None:
        cur = pole(G, X, j, '-')
        if cur != new_src:
            if j == 0:
                raise LiftFailure('object poles differ')
            k = cmp(G, infer(G, cur), new_src, cur)
            if k is None:
                raise LiftFailure('no comparison at rank %d' % j)
            X = comp2(G, j, k, X)
    if new_tgt is not None:
        cur = pole(G, X, j, '+')
        if cur != new_tgt:
            if j == 0:
                raise LiftFailure('object poles differ')
            k = cmp(G, infer(G, cur), cur, new_tgt)
            if k is None:
                raise LiftFailure('no comparison at rank %d' % j)
            X = comp2(G, j, X, k)
    return X

def lift_word(G, w, cmp):
    if w[0] == 'atom':
        return v(w[1])
    if w[0] == 'id':
        import rc_oracle
        return rc_oracle.identity(G, lift_word(G, w[1], cmp))
    _, r, w1, w2 = w
    X1, X2 = lift_word(G, w1, cmp), lift_word(G, w2, cmp)
    for j in range(r):
        X2 = adjust(G, X2, j, pole(G, X1, j, '-'), pole(G, X1, j, '+'), cmp)
    X2 = adjust(G, X2, r, pole(G, X1, r, '+'), None, cmp)
    return comp2(G, r, X1, X2)

def lift_at(G, c, s, t, cmp, K=None):
    """A raw term with strict value c (a tableau of rank d >= 1) and literal
    poles s -> t (raw (d-1)-terms), using comparisons of rank < d."""
    K = K or St.Complex(G)
    w = St.strict_word(K, c)
    X = lift_word(G, w, cmp)
    d = St.cdim(c)
    for j in range(d - 1):
        X = adjust(G, X, j, pole(G, s, j, '-'), pole(G, s, j, '+'), cmp)
    X = adjust(G, X, d - 1, s, t, cmp)
    assert infer(G, X)[2:] == (s, t)
    return X

# ---------------------------------------------------------------- padding removal (r9 Response 2)

def id_tower(G, x, j):
    """1^j_x: the j-dimensional iterated identity on a term x."""
    import rc_oracle
    t = x
    while term_dim(G, t) < j:
        t = rc_oracle.identity(G, t)
    return t

def R_pad(G, x):
    """R_j(x) = x *_0 1^j_{t_0 x} for a j-term x, j > 0."""
    j = term_dim(G, x)
    return comp2(G, 0, x, id_tower(G, pole(G, x, 0, '+'), j))

_PLM = {}
def PLM(j):
    """Over the generic j-disk D^j (top variable last): P_j(x), L_j : x -> P_j(x),
    M_j : P_j(x) -> x."""
    if j in _PLM:
        return _PLM[j]
    D = tree_ctx(disc_tree(j))
    x = v(len(D) - 1)
    P = R_pad(D, x)
    for i in range(1, j):
        Pi, Li, Mi = PLM(i)
        Li_s = inst(D, i, Li, pole(D, x, i, '-'))
        Mi_t = inst(D, i, Mi, pole(D, x, i, '+'))
        P = comp2(D, i, comp2(D, i, Li_s, P), Mi_t)
    A = infer(D, x)
    assert infer(D, P) == A, 'P_j not parallel to x'
    L = ('coh', D, arr(A, x, P), tuple(v(k) for k in range(len(D))))
    M = ('coh', D, arr(A, P, x), tuple(v(k) for k in range(len(D))))
    _PLM[j] = (P, L, M)
    return _PLM[j]

def inst(G, j, T, y):
    """Instantiate a term T over D^j at the j-term y of G."""
    D = tree_ctx(disc_tree(j))
    return subst_tm(T, sub_from(D, G, {len(D) - 1: y}))

def unpad(G, H, u, v_):
    """From H : R_n(u) -> R_n(v) (with the padding of Response 2), the comparison
    u -> v: whisker at cuts i = 1..n by L_i(s_i u) on the left and M_i(t_i v) on
    the right."""
    n = term_dim(G, u)
    X = H
    for i in range(1, n + 1):
        Pi, Li, Mi = PLM(i)
        left = inst(G, i, Li, pole(G, u, i, '-') if i < n else u)
        right = inst(G, i, Mi, pole(G, v_, i, '+') if i < n else v_)
        X = comp2(G, i, comp2(G, i, left, X), right)
    assert infer(G, X)[2:] == (u, v_), 'unpad: wrong poles'
    return X

def attach_globe(G, y, n):
    """G extended by an n-globe whose initial vertex is y. Returns (G', z, collapse)
    with z the top variable and collapse : G' -> G fixing G and sending the
    globe's j-variables to 1^j_y."""
    D = tree_ctx(disc_tree(n))
    base = len(G)
    ren = {0: y}
    for k in range(1, len(D)):
        ren[k] = base + k - 1
    def rt(t):
        if t[0] == 'v': return v(ren[t[1]])
        return ('coh', t[1], t[2], tuple(rt(a) for a in t[3]))
    def rty(A):
        if A == STAR: return A
        return arr(rty(A[1]), rt(A[2]), rt(A[3]))
    G2 = tuple(G) + tuple(rty(D[k]) for k in range(1, len(D)))
    z = v(base + len(D) - 2)
    col = [v(i) for i in range(len(G))]
    for k in range(1, len(D)):
        col.append(id_tower(G, v(y), tdim(D[k]) + 1))
    return G2, z, tuple(col)

def via_globe(G, u, v_, intrinsic_rc):
    """Response 2: a comparison u -> v of parallel n-terms of equal value, from
    a comparison u *_0 z -> v *_0 z (intrinsic value) supplied by intrinsic_rc
    in G extended by a fresh n-globe at y = t_0 u."""
    n = term_dim(G, u)
    y = pole(G, u, 0, '+')[1]
    G2, z, col = attach_globe(G, y, n)
    a, b = comp2(G2, 0, u, z), comp2(G2, 0, v_, z)
    K = intrinsic_rc(G2, infer(G2, a), a, b)
    if K is None:
        return None
    H = subst_tm(K, col)
    assert infer(G, H)[2:] == (R_pad(G, u), R_pad(G, v_)), 'collapse: wrong poles'
    return unpad(G, H, u, v_)
