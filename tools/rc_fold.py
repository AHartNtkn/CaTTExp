"""Folding a free generator (r9 Response 4, "Constructing all the local
fillings", free source case). Untrusted oracle code: every result is
type-checked by catt.infer.

Given a context variable v : x -> p (rank m) whose source x is a variable
used by no other declaration (a free source), two parallel rank-(m+1)
tracks H0, H1 : u -> w are compared through the fold x := p, v := 1_p:

  H_i *_m k_w  --H_i^-->  k_u *_m (s^ *_{m-1} H_i+)

are the depth-two naturality squares (rc_nat.square with Y = {x, v},
x^ = v and v^ the inverse right unitor v -> v * 1_p); the folded tracks
H_i+ are compared by `inner`, and the common suffix k_w is cancelled with
rc_inverse.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from catt import *

def _R():
    import rc_oracle
    return rc_oracle

def free_sources(G):
    """Pairs (x, v): v : x -> p a declaration whose source is the variable x,
    with x used in no other declaration."""
    out = []
    for vv, T in enumerate(G):
        if T == STAR or T[2][0] != 'v':
            continue
        x = T[2][1]
        users = [j for j, S in enumerate(G) if S != STAR and x in fv_ty(S)]
        if users == [vv] and x not in fv_tm(T[3]):
            out.append((x, vv))
    return out

def fold_compare(G, A, H0, H1, x, vv, rec, inner):
    """H0 -> H1 through the fold of (x, vv); None if a step fails."""
    import rc_nat as N, rc_inverse as I
    R = _R()
    n = tdim(A) + 1                       # rank of the tracks
    p = G[vv][3]
    one = R.identity(G, p)
    runit = rec(G, infer(G, v(vv)), v(vv), comp2(G, tdim(G[vv]), v(vv), one))
    if runit is None:
        return None
    Y = {x, vv}
    pm = {x: p, vv: one}
    um = {x: v(vv), vv: runit}
    try:
        w0, a0, b0 = N.square(G, Y, pm, um, H0, rec)
        w1, a1, b1 = N.square(G, Y, pm, um, H1, rec)
    except (N.NoFiller, TypeError_, AssertionError, KeyError, ValueError) as e:
        _dbg('square', type(e).__name__)
        return None
    plus = tuple(pm.get(i, v(i)) for i in range(len(G)))
    P0, P1 = subst_tm(H0, plus), subst_tm(H1, plus)
    if P0 == P1:
        Xp = None
    else:
        Xp = inner(G, infer(G, P0), P0, P1)
        if Xp is None:
            _dbg('inner failed')
            return None
    # b0 = k_u *_{n-1} (s^ *_{n-2} P0): replace P0 by P1 inside
    if Xp is not None:
        mid = R.vfactors(G, b0, n)
        # b_i = [k_u-part..., s^ * P_i]: whisker Xp by s^ (if any) then by k_u
        ku = N.nat_in(G, frozenset(Y), pm, um, A[2], rec)
        s_ = infer(G, A[2])[2]
        W = Xp
        if s_ != subst_tm(s_, plus) or (fv_tm(s_) & Y):
            sl = N.nat_in(G, frozenset(Y), pm, um, s_, rec)
            W = comp2(G, n - 2, sl, W)
        W = comp2(G, n - 1, ku, W)
        if src(G, W) != b0 or tgt(G, W) != b1:
            x1 = rec(G, infer(G, b0), b0, src(G, W)) if src(G, W) != b0 else None
            x2 = rec(G, infer(G, b1), tgt(G, W), b1) if tgt(G, W) != b1 else None
            if (src(G, W) != b0 and x1 is None) or (tgt(G, W) != b1 and x2 is None):
                _dbg('whisker ends', x1 is None, x2 is None)
                return None
            W = _chain(G, n + 1, [x1, W, x2])
    else:
        W = None
    w1i = I.inverse(G, w1)
    if w1i is None:
        _dbg('square inverse')
        return None
    Y0 = _chain(G, n + 1, [w0, W, w1i])          # H0 * k_w -> H1 * k_w
    # cancel the common suffix k_w
    kw = N.nat_in(G, frozenset(Y), pm, um, A[3], rec)
    kwi = I.inverse(G, kw)
    cw = I.cancel(G, kw, rec)                     # kw * kwi -> 1
    if kwi is None or cw is None:
        _dbg('kw inverse/cancel', kwi is None, cw is None)
        return None
    ins = I.inverse(G, cw)                        # 1 -> kw * kwi
    one_w = R.identity(G, A[3])
    # H0 -> H0 * 1 -> H0 * (kw * kwi) -> (H0 * kw) * kwi -> (H1 * kw) * kwi -> H1 * (kw * kwi) -> H1 * 1 -> H1
    m = n - 1
    H01 = comp2(G, m, H0, one_w)
    st = []
    st.append(rec(G, A, H0, H01))
    st.append(comp2(G, m, H0, ins))
    a_ = comp2(G, m, H0, comp2(G, m, kw, kwi))
    b_ = comp2(G, m, comp2(G, m, H0, kw), kwi)
    st.append(rec(G, A, a_, b_))
    st.append(comp2(G, m, Y0, kwi))
    a2 = comp2(G, m, comp2(G, m, H1, kw), kwi)
    b2 = comp2(G, m, H1, comp2(G, m, kw, kwi))
    st.append(rec(G, A, a2, b2))
    st.append(comp2(G, m, H1, cw))
    st.append(rec(G, A, comp2(G, m, H1, one_w), H1))
    if any(y is None for y in st):
        _dbg('final steps', [y is None for y in st])
        return None
    return _chain(G, n + 1, st)

DEBUG = [False]
def _dbg(*a):
    if DEBUG[0]:
        print('rc_fold:', *a, flush=True)

def _chain(G, d, cells):
    """Vertical composite (along d-1... i.e. of d-cells along d-1) of the
    non-None cells, checking that consecutive ends meet."""
    cells = [c for c in cells if c is not None]
    out = cells[0]
    for c in cells[1:]:
        assert tgt(G, out) == src(G, c), 'fold: ends do not meet'
        out = comp2(G, d - 1, out, c)
    return out
