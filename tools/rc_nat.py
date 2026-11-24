"""
Naturality lifts t↑ (conjectures/naturality-arbitrary-depth.md §2-§3,
relative-coherence.md §4.1 Proposition R), executable.

Given a context G, an up-closed set Y of variables of G, and for every
y in Y a term plus[y] (the copy y⁺) and a term up[y] : a_y -> b_y (the
cylinder y↑), all in a context H that contains G as a prefix, nat(t)
returns t↑ : a_t -> b_t in H for every term t of G meeting Y.

The only non-syntactic ingredient is, for each coherence c = coh_{Q,B}
occurring in t, a filler K(Q, B, Y') : a_c -> b_c in the cylinder context
Q↑Y'. These are asked of the RC oracle in that small generic context
(Proposition R: π(a_c) = π(b_c) for a coherence c). They are cached by
(Q, B, Y'). Every answer is type-checked by catt.infer.

Used to move an event (the action of a cell e : x -> x′) across a block of
caps: for a cap C meeting x, C↑ : C ∗_{n-1} (τC)↑ -> (σC)↑ ∗_{n-1} C⁺ is the
naturality square.

Composition case (Proposition R): the filler is the layered composite of
the generators' lifts q↑, each layer being c itself with one slot widened
(coh over the extended pasting context), joined by RC connectors, all in
the small cylinder context. Lower-dimensional whiskers meeting Y in a
layer are not handled (NoFiller). nat_op gives oplax squares b_t -> a_t for
terms whose top-dimensional structure is coherences and their composites.
Reassociation case (_assoc_filler): a coherence over a vertical chain whose
two sides are bracketings of the top cells with identities inserted is
transferred from a composite of small unitor, associator and sub-chain heads
along the coherences between the two, with no search in the cylinder.
sweep / sweep_rc move an event across a block of caps that differ by one
variable renaming x -> x′ with a context cell x -> x′.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from catt import *

class NoFiller(Exception):
    pass

_K = {}
SMALL_CYL = [40]

def rename_map(w, m, memo=None):
    """w with variables renamed by m (index -> term), preserving sharing:
    the terms built here are deeply shared, and a tree walk is exponential.
    Pass one memo for repeated calls with the same m."""
    if memo is None:
        memo = {}
    def go(x):
        r = memo.get(id(x))
        if r is not None:
            return r[1]
        if x[0] == 'v':
            y = m.get(x[1], x)
        else:
            y = ('coh', x[1], x[2], tuple(go(u) for u in x[3]))
        memo[id(x)] = (x, y)
        return y
    return go(w)

def _iter_tgt(H, t, k):
    for _ in range(k):
        t = tgt(H, t)
    return t

def _iter_src_then(H, t, k):
    # σ^k t (all sources)
    for _ in range(k):
        t = src(H, t)
    return t

def boundary_ab(H, t, meets, lift, plus):
    """a_t, b_t of §2.2 for a term t of H (dimension n >= 0).
    meets(w): does w meet Y; lift(w): w↑; plus(w): w⁺."""
    n = tdim_tm(H, t)
    if n == 0:
        return t, plus(t)
    a = t
    # a_t = (...((t⁻ *₀ (τⁿ t)↑) *₁ (τⁿ⁻¹ t)↑) ...) *_{n-1} (τ t)↑
    for j in range(n):            # j = 0 .. n-1 ; factor (τ^{n-j} t)↑ along j
        w = _iter_tgt(H, t, n - j)
        if meets(w):
            a = comp2(H, j, a, lift(w))
    # b_t = (σ t)↑ *_{n-1} ( ... ((σⁿ⁻¹ t)↑ *₁ ((σⁿ t)↑ *₀ t⁺)) ... )
    b = plus(t)
    for j in range(n):
        w = _iter_src_then(H, t, n - j)
        if meets(w):
            b = comp2(H, j, lift(w), b)
    return a, b

def cylinder(Q, Y, op_tops=frozenset()):
    """The cylinder context Q↑Y of a pasting context Q, up-closed Y.
    Returns (C, mi, pl, up): mi[q], pl[q] are the indices of q⁻ (or q) and
    q⁺ (or q), up[q] the index of q↑ (q in Y)."""
    C = []
    mi, pl, up = {}, {}, {}
    def ren(t, m):
        return subst_tm(t, tuple(v(m[i]) for i in range(len(m)))) if False else _ren(t, m)
    for q, A in enumerate(Q):
        if q not in Y:
            B = _ren_ty(A, mi)
            mi[q] = pl[q] = len(C); C.append(B)
            continue
        Am = _ren_ty(A, mi); Ap = _ren_ty(A, pl)
        mi[q] = len(C); C.append(Am)
        pl[q] = len(C); C.append(Ap)
        Ct = tuple(C)
        Ymin = frozenset(mi[y] for y in Y if y in mi)
        meets = lambda w: bool(fv_tm(w) & Ymin)
        def lift(w):
            assert w[0] == 'v', 'boundary of a pasting-context variable is a variable'
            qq = _inv(mi, w[1])
            return v(up[qq])
        def plus(w):
            return _swap(w, mi, pl, Y)
        a, b = boundary_ab(Ct, v(mi[q]), meets, lift, plus)
        if q in op_tops:
            up[q] = len(C); C.append(arr(infer(Ct, a), b, a))
        else:
            up[q] = len(C); C.append(arr(infer(Ct, a), a, b))
    return tuple(C), mi, pl, up

def _Yimg(Y, mi, pl):
    return frozenset([mi[y] for y in Y if y in mi] + [pl[y] for y in Y if y in pl])

def _inv(m, i):
    for k, j in m.items():
        if j == i:
            return k
    raise KeyError(i)

def _ren(t, m):
    if t[0] == 'v':
        return v(m[t[1]])
    return ('coh', t[1], t[2], tuple(_ren(u, m) for u in t[3]))

def _ren_ty(A, m):
    if A == STAR:
        return A
    return arr(_ren_ty(A[1], m), _ren(A[2], m), _ren(A[3], m))

def _swap(t, mi, pl, Y):
    """t (over the q⁻ copies) -> its q⁺ copy."""
    back = {}
    for q in mi:
        if pl[q] != mi[q]:
            back[mi[q]] = v(pl[q])
    return rename_map(t, back)

def _extend_leaf(tree, q):
    """The tree with the leaf whose arrow variable is q given one child, so
    q becomes the source of a new top variable θ : q -> q′ (indices q+1 = q′,
    q+2 = θ; old indices above q shift by 2)."""
    counter = [1]
    def go(node):
        out = []
        for child in node:
            counter[0] += 1          # y
            f = counter[0]; counter[0] += 1
            if f == q:
                assert child == (), 'q is not a top variable'
                out.append(((),))
                counter[0] += 0
            else:
                out.append(go(child))
        return tuple(out)
    return go(tree)

def _is_composition(Q, B):
    return (fv_ty(B) | fv_tm(B[2]) | fv_tm(B[3])) != frozenset(range(len(Q)))

def _composition_filler(Q, B, Yq, C, mi, pl, up, a, b, rc):
    """Proposition R, composition case, for Y meeting Q only in top-dimensional
    variables (so a_c = c⁻, b_c = c⁺): the layered composite of the whiskered
    q↑, in reverse pasting order, joined by RC connectors."""
    n = ps_dim(Q)
    tops = [q for q in sorted(Yq, reverse=True)]
    if any(tdim(Q[q]) + 1 != n for q in Yq):
        raise NoFiller(('composition with lower Y-variables', len(Q)))
    tree = tree_of(Q)
    U = ucomp(Q)
    done = set()
    layers = []
    for q in tops:
        Qq = tree_ctx(_extend_leaf(tree, q))
        Uq = ucomp(Qq)
        sub = []
        for i in range(len(Q)):
            if i == q:
                sub.append(v(mi[i]))                       # q -> q⁻
                sub.append(v(pl[i]))                       # q′ -> q⁺
                sub.append(v(up[i]))                       # θ -> q↑
            elif i in Yq:
                sub.append(v(pl[i] if i in done else mi[i]))
            else:
                sub.append(v(mi[i]))
        layers.append(subst_tm(Uq, tuple(sub)))
        done.add(q)
    # chain: a -> src L1, L1, tgt L1 -> src L2, ..., tgt Lr -> b
    pieces = []
    cur = a
    for L in layers:
        s_ = src(C, L)
        if s_ != cur:
            w = rc(C, infer(C, cur), cur, s_)
            if w is None:
                raise NoFiller(('connector', len(Q)))
            pieces.append(w)
        pieces.append(L)
        cur = tgt(C, L)
    if cur != b:
        w = rc(C, infer(C, cur), cur, b)
        if w is None:
            raise NoFiller(('connector', len(Q)))
        pieces.append(w)
    K = pieces[0]
    for P_ in pieces[1:]:
        K = comp2(C, n, K, P_)
    return K

def _layered(Q, B, Yq, C, mi, pl, up, a, b, rc, op):
    n = ps_dim(Q)
    tops = [q for q in range(len(Q)) if q in Yq and tdim(Q[q]) + 1 == n]
    order = tops if op else list(reversed(tops))
    tree = tree_of(Q)
    done = set()
    pieces, cur = [], (b if op else a)
    for q in order:
        Qq = tree_ctx(_extend_leaf(tree, q))
        shift = lambda i: i if i < q else (i + 2 if i > q else i)
        images = {q + 2: v(up[q])}
        for i in maximal_vars(Q):
            if i == q:
                continue
            if i in Yq and tdim(Q[i]) + 1 < n:
                raise NoFiller('layer with a lower-dimensional Y-whisker')
            if i in Yq:
                before = (i in done)
                # op: processed slots are back to minus; lax: processed slots are plus
                images[shift(i)] = v(mi[i]) if (before == op) else v(pl[i])
            else:
                images[shift(i)] = v(mi[i])
        sub = sub_from(Qq, C, images)
        # the layer is c itself with slot q widened to θ : q -> q′, so that
        # consecutive layers meet literally
        state = {}
        for i in range(len(Q)):
            state[i] = shift(i)
        cs = ('coh', Q, B, tuple(v(state[i]) for i in range(len(Q))))
        ct = ('coh', Q, B, tuple(v(q + 1) if i == q else v(state[i]) for i in range(len(Q))))
        L0 = ('coh', Qq, arr(infer(Qq, cs), cs, ct), tuple(v(i) for i in range(len(Qq))))
        L = subst_tm(L0, sub)
        s_ = src(C, L)
        if s_ != cur:
            w = rc(C, infer(C, cur), cur, s_)
            if w is None:
                raise NoFiller(('connector', len(Q)))
            pieces.append(w)
        pieces.append(L)
        cur = tgt(C, L)
        done.add(q)
    end = a if op else b
    if cur != end:
        w = rc(C, infer(C, cur), cur, end)
        if w is None:
            raise NoFiller(('connector', len(Q)))
        pieces.append(w)
    if not pieces:
        raise NoFiller('no top-dimensional Y-variable in the layers')
    K = pieces[0]
    for P_ in pieces[1:]:
        K = comp2(C, n, K, P_)
    return K

def _lifted(C, n, Yq, Q, up, s_, t_, rc):
    """Composition case by prescribed-boundary lifting (r9 Response 2): the
    strict cell of c^ has top chain the sum of the q^ for the top-dimensional
    q in Y; lift it at the raw poles s_ -> t_ in the cylinder C, with
    comparisons of smaller rank from rc."""
    import rc_oracle as R, rc_lift as L, steiner as St
    ups = [up[q] for q in Yq if tdim(Q[q]) + 1 == n]
    chain = tuple(sorted((u, 1) for u in ups))
    try:
        cell = St.image_to_cell((n + 1, chain, R.strict_image(C, s_), R.strict_image(C, t_)))
        return L.lift_at(C, cell, s_, t_, rc)
    except Exception:
        return None

def _vchain_heads(Q):
    """The binary vertical-composition head at the top dimension d of Q, if
    Q is a d-chain (a single column of top cells over a common (d-1)-globe)."""
    d = ps_dim(Q)
    if d < 1:
        return None
    tops = [q for q in maximal_vars(Q)]
    if any(tdim(Q[q]) + 1 != d for q in tops) or len(tops) < 4:
        return None
    x = comp2(Q, d - 1, v(tops[0]), v(tops[1]))
    if x[0] != 'coh':
        return None
    P2 = x[1]
    return d, (P2, x[2]), [i for i in maximal_vars(P2)]

def _assoc_filler(Q, B, Yq, C, mi, pl, up, a, b, rc, op=False):
    """A coherence c : P => P' over a d-chain Q whose two sides are binary
    bracketings of the top cells (a reassociation). Its filler is transferred
    from the composite c' of elementary associators P => N <= P' (N the
    left-nested bracketing): c'^ is built by nat_in from small heads, and
    gamma : c => c' (a coherence over Q) whiskers a_c -> a_c' and b_c' -> b_c.
    Returns None if c is not of this form."""
    hv = _vchain_heads(Q)
    if hv is None or B[0] != '->':
        return None
    d, head, mx2 = hv
    if tdim(B) != d:
        return None
    def is_unit(x):
        return (x[0] == 'coh' and x[2][2] == x[2][3] and tdim(x[2]) + 1 == d
                and len(x[1]) == len(x[3]) and ps_dim(x[1]) == d - 1)
    def parse(x):
        if x[0] == 'v':
            return x[1] if tdim(Q[x[1]]) + 1 == d else None
        if is_unit(x):
            return ('U', x)
        if (x[1], x[2]) != head:
            return None
        l, r = parse(x[3][mx2[0]]), parse(x[3][mx2[1]])
        if l is None or r is None:
            return None
        return (l, r)
    TP, TQ = parse(B[2]), parse(B[3])
    if TP is None or TQ is None:
        return None
    def build(T):
        if isinstance(T, int):
            return v(T)
        if T[0] == 'U':
            return T[1]
        return comp2(Q, d - 1, build(T[0]), build(T[1]))
    isU = lambda T: not isinstance(T, int) and T[0] == 'U'
    # the unitors over the 1-chain P1 (one top cell f : x0 -> x1)
    P1 = head[0][:mx2[0] + 1]
    f1 = P1[mx2[0]]
    ix0, ix1 = f1[2][1], f1[3][1]
    Dd = P1[:ix0 + 1]
    def idat(i):
        return ('coh', Dd, arr(Dd[ix0], v(ix0), v(ix0)), tuple(v(j) for j in range(ix0)) + (v(i),))
    def unitor(X, left, back):
        # left: id * X => X ; right: X * id => X ; back reverses
        fx = v(mx2[0])
        s_ = comp2(P1, d - 1, idat(ix0), fx) if left else comp2(P1, d - 1, fx, idat(ix1))
        st_, tt_ = (fx, s_) if back else (s_, fx)
        h_ = ('coh', P1, arr(infer(P1, st_), st_, tt_), tuple(v(j) for j in range(len(P1))))
        return subst_tm(h_, sub_from(P1, Q, {mx2[0]: X}))
    def strip(T, back):
        # steps T => T' (T' without units unless T is all units); back: reversed steps
        if isinstance(T, int) or isU(T):
            return T, []
        L, R = T
        L2, sL = strip(L, back)
        R2, sR = strip(R, back)
        st = [comp2(Q, d - 1, w, build(R)) for w in sL]
        st += [comp2(Q, d - 1, build(L2), w) for w in sR]
        if isU(L2):
            st.append(unitor(build(R2), True, back))
            return R2, st
        if isU(R2):
            st.append(unitor(build(L2), False, back))
            return L2, st
        return (L2, R2), st
    if build(TP) != B[2] or build(TQ) != B[3]:
        return None
    if (TP == TQ):
        return None
    # the elementary associator over a 3-chain of top cells
    def chain3():
        P2 = head[0]
        g = P2[mx2[1]]                       # arr(base, x1, x2)
        base, ix2 = g[1], g[3][1]
        P = list(P2)
        P.append(P2[ix2])                    # x3, parallel to x2
        P.append(arr(base, v(ix2), v(len(P) - 1)))
        return tuple(P)
    P3 = chain3()
    assert is_ps(P3), 'chain3'
    t3 = maximal_vars(P3)
    f, g, h = (v(i) for i in t3)
    l3 = comp2(P3, d - 1, comp2(P3, d - 1, f, g), h)
    r3 = comp2(P3, d - 1, f, comp2(P3, d - 1, g, h))
    def assoc(X, Y, Z, back):
        # X(YZ) => (XY)Z, or reversed
        s_, t_ = (l3, r3) if back else (r3, l3)
        al = ('coh', P3, arr(infer(P3, s_), s_, t_), tuple(v(i) for i in range(len(P3))))
        imgs = {t3[0]: X, t3[1]: Y, t3[2]: Z}
        return subst_tm(al, sub_from(P3, Q, imgs))
    def merge(X, Y, back):
        # normal X, Y: steps X∘Y => normal of X∘Y (or reversed steps); returns (N, steps)
        if isinstance(Y, int):
            return (X, Y), []
        Bt, c = Y
        st = [assoc(build(X), build(Bt), build(c), back)]
        Nxb, s2 = merge(X, Bt, back)
        st += [comp2(Q, d - 1, w, build(c)) for w in s2]
        return (Nxb, c), st
    def norm(T, back):
        if isinstance(T, int):
            return T, []
        L, R = T
        NL, sL = norm(L, back)
        NR, sR = norm(R, back)
        st = [comp2(Q, d - 1, w, build(R)) for w in sL]
        st += [comp2(Q, d - 1, build(NL), w) for w in sR]
        N, sm = merge(NL, NR, back)
        return N, st + sm
    def chaink(k):
        P2 = head[0]
        g = P2[mx2[1]]
        base, ix = g[1], g[3][1]
        P = list(P2)
        for _ in range(k - 2):
            P.append(P[ix])
            P.append(arr(base, v(ix), v(len(P) - 1)))
            ix = len(P) - 2
        return tuple(P)
    def leaves(T):
        return [T] if isinstance(T, int) else leaves(T[0]) + leaves(T[1])
    def subcoh(T1, T2):
        # the coherence T1 => T2 over the sub-chain of their leaves, as one small head
        ls = leaves(T1)
        Pk = chaink(len(ls))
        tk = maximal_vars(Pk)
        ren_ = dict(zip(ls, tk))
        def rb(T):
            return v(ren_[T]) if isinstance(T, int) else comp2(Pk, d - 1, rb(T[0]), rb(T[1]))
        s_, t_ = rb(T1), rb(T2)
        h_ = ('coh', Pk, arr(infer(Pk, s_), s_, t_), tuple(v(i) for i in range(len(Pk))))
        return subst_tm(h_, sub_from(Pk, Q, {tk[i]: v(ls[i]) for i in range(len(ls))}))
    def diff(T1, T2):
        # steps T1 => T2: split at a common root, else rotate through the normal form
        if T1 == T2:
            return []
        if not isinstance(T1, int) and leaves(T1[0]) == leaves(T2[0]):
            st = []
            if T1[0] != T2[0]:
                st.append(comp2(Q, d - 1, subcoh(T1[0], T2[0]), build(T1[1])))
            if T1[1] != T2[1]:
                st.append(comp2(Q, d - 1, build(T2[0]), subcoh(T1[1], T2[1])))
            return st
        N1, s1 = norm(T1, False)
        N2, s2 = norm(T2, True)
        assert N1 == N2
        return s1 + list(reversed(s2))
    SP, stP = strip(TP, False)
    SQ, stQ = strip(TQ, True)
    if isU(SP) or isU(SQ) or (stP or stQ) and SP == TP and SQ == TQ:
        return None
    steps = stP + diff(SP, SQ) + list(reversed(stQ))
    if not steps or (len(steps) == 1 and steps[0][0] == 'coh' and steps[0][1] == Q):
        return None
    cprime = steps[0]
    for w in steps[1:]:
        cprime = comp2(Q, d, cprime, w)
    assert infer(Q, cprime) == B, 'reassociation composite'
    return _transfer(Q, B, Yq, C, mi, pl, up, a, b, rc, cprime, op)

def _transfer(Q, B, Yq, C, mi, pl, up, a, b, rc, cprime, op=False):
    """The filler of c = coh(Q, B) from that of a parallel term c' of Q,
    along the coherences gamma : c => c' and c' => c over Q (both full):
    a_c -> a_c' (gamma whiskered by the target lifts), c'^, then
    b_c' -> b_c (gamma^-1 on the plus side, whiskered by the source lifts)."""
    n = tdim(B) + 1
    c = ('coh', Q, B, tuple(v(i) for i in range(len(Q))))
    g_fw = ('coh', Q, arr(B, c, cprime), tuple(v(i) for i in range(len(Q))))
    g_bw = ('coh', Q, arr(B, cprime, c), tuple(v(i) for i in range(len(Q))))
    ren = lambda t: _ren(t, mi)
    Yimg = frozenset(mi[q] for q in Yq)
    meets = lambda w: bool(fv_tm(w) & Yimg)
    plus = lambda w: _swap(w, mi, pl, Yq)
    _pm, _um, _lm = {mi[q]: v(pl[q]) for q in Yq}, {mi[q]: v(up[q]) for q in Yq}, {}
    lift = lambda w: nat_in(C, Yimg, _pm, _um, w, rc, _lm)
    def a_side(g):
        for j in range(n):
            w_ = _iter_tgt(C, ren(c), n - j)
            if meets(w_):
                g = comp2(C, j, g, lift(w_))
        return g
    def b_side(g):
        for j in range(n):
            w_ = _iter_src_then(C, ren(c), n - j)
            if meets(w_):
                g = comp2(C, j, lift(w_), g)
        return g
    if not op:
        Kp = lift(ren(cprime))
        K = comp2(C, n, comp2(C, n, a_side(ren(g_fw)), Kp), b_side(plus(ren(g_bw))))
        ok = infer(C, K) == arr(infer(C, a), a, b)
    else:
        # oplax: b_c -> b_c' -> (c'^op) -> a_c' -> a_c
        Kp, _, _ = nat_op(C, Yimg, {mi[q]: v(pl[q]) for q in Yq}, {mi[q]: v(up[q]) for q in Yq}, ren(cprime), rc)
        K = comp2(C, n, comp2(C, n, b_side(plus(ren(g_fw))), Kp), a_side(ren(g_bw)))
        ok = infer(C, K) == arr(infer(C, a), b, a)
    return K if ok else None

def _bincomp(Q):
    """The composite of the pasting context Q by binary composites, following
    its tree: at a k-cell the children are composed left to right by *_k."""
    tree = tree_of(Q)
    nxt = [1]
    def go(node, k):
        terms = []
        for child in node:
            f = nxt[0] + 1
            nxt[0] += 2
            terms.append(go(child, k + 1) if child else v(f))
        acc = terms[0]
        for t in terms[1:]:
            acc = comp2(Q, k, acc, t)
        return acc
    return go(tree, 0)

def _binary_filler(Q, B, Yq, C, mi, pl, up, a, b, rc, op=False):
    """A composition head c = coh(Q, B) with a large cylinder: transfer from
    c'' = the binary composite of Q, its poles adjusted to those of c by
    comparisons of lower rank in Q (Response 2's adjust); the lifts of the
    binary heads have small cylinders."""
    import rc_lift as L
    n = tdim(B) + 1
    cb = _bincomp(Q)
    if tdim_tm(Q, cb) != n:
        return None
    s_, t_ = B[2], B[3]
    try:
        for j in range(n - 1):
            cb = L.adjust(Q, cb, j, L.pole(Q, s_, j, '-'), L.pole(Q, s_, j, '+'), rc)
        cb = L.adjust(Q, cb, n - 1, s_, t_, rc)
    except L.LiftFailure:
        return None
    if infer(Q, cb) != B or cb == ('coh', Q, B, tuple(v(i) for i in range(len(Q)))):
        return None
    return _transfer(Q, B, Yq, C, mi, pl, up, a, b, rc, cb, op)

def filler(Q, B, Yq, rc, op=False):
    key = (Q, B, frozenset(Yq), op)
    if key in _K:
        if _K[key] is None:
            raise NoFiller(key)
        return _K[key]
    comp = _is_composition(Q, B)
    n = ps_dim(Q)
    optops = frozenset(q for q in Yq if tdim(Q[q]) + 1 == n) if (op and comp) else frozenset()
    C, mi, pl, up = cylinder(Q, Yq, optops)
    c = ('coh', Q, B, tuple(v(mi[i]) for i in range(len(Q))))
    Yimg = frozenset(mi[q] for q in Yq)
    meets = lambda w: bool(fv_tm(w) & Yimg)
    def plus(w):
        return _swap(w, mi, pl, Yq)
    _pm, _um, _lm = {mi[q]: v(pl[q]) for q in Yq}, {mi[q]: v(up[q]) for q in Yq}, {}
    def lift(w):
        return nat_in(C, Yimg, _pm, _um, w, rc, _lm)
    a, b = boundary_ab(C, c, meets, lift, plus)
    A = infer(C, a)
    if comp:
        try:
            w = _layered(Q, B, Yq, C, mi, pl, up, a, b, rc, op)
        except (NoFiller, TypeError_):
            w = None
            if len(C) > SMALL_CYL[0]:
                try:
                    w = _binary_filler(Q, B, Yq, C, mi, pl, up, a, b, rc, op)
                except NoFiller:
                    w = None
            if w is None:
                w = _lifted(C, n, Yq, Q, up, b if op else a, a if op else b, rc)
            if w is None and len(C) <= SMALL_CYL[0]:
                # a small cylinder (e.g. a whiskering head with a moving
                # lower whisker): ask the comparison directly
                w = rc(C, A, b, a) if op else rc(C, A, a, b)
            if w is None:
                _K[key] = None
                raise NoFiller(key)
    elif op:
        w = None
        try:
            w = _assoc_filler(Q, B, Yq, C, mi, pl, up, a, b, rc, op=True)
        except NoFiller:
            w = None
        if w is None:
            w = rc(C, A, b, a)
    else:
        w = None
        try:
            w = _assoc_filler(Q, B, Yq, C, mi, pl, up, a, b, rc)
        except NoFiller:
            w = None
        if w is None:
            w = rc(C, A, a, b)
    if w is None:
        _K[key] = None
        raise NoFiller((Q, B, tuple(sorted(Yq))))
    _K[key] = (C, mi, pl, up, w, optops)
    return _K[key]
    

def nat_in(H, Y, plus_map, up_map, t, rc, memo=None):
    """t↑ in H, for Y ⊆ Var(H) up-closed among the variables t uses,
    with y⁺ = plus_map[y], y↑ = up_map[y]. Pass one memo (a dict) for
    repeated calls with the same data: lifts are shared across calls."""
    if memo is None:
        memo = {}
    def meets(w):
        return bool(fv_tm(w) & Y)
    pmemo = {}
    def plus(w):
        return rename_map(w, plus_map, pmemo)
    def lift(w):
        hit = memo.get(id(w))
        if hit is not None:
            return hit[1]
        if w[0] == 'v':
            r = up_map[w[1]]
        else:
            Q, B, g = w[1], w[2], w[3]
            Yq = frozenset(q for q in range(len(Q)) if meets(g[q]))
            # up-closure inside Q (types mention lower variables)
            changed = True
            while changed:
                changed = False
                for q, A in enumerate(Q):
                    if q not in Yq and A != STAR and (fv_ty(A) & Yq):
                        Yq = Yq | {q}; changed = True
            C, mi, pl, up, K, _ = filler(Q, B, Yq, rc)
            sub = [None] * len(C)
            for q in range(len(Q)):
                sub[mi[q]] = g[q]
                if q in Yq:
                    sub[pl[q]] = plus(g[q])
                    sub[up[q]] = lift(g[q])
            r = subst_tm(K, tuple(sub))
        memo[id(w)] = (w, r)
        return r
    return lift(t)

def nat_op(H, Y, plus_map, up_map, t, rc, down_map=None):
    """The oplax square t↑ᵒᵖ : b_t -> a_t, for t whose top-dimensional
    structure is coherences (caps) and compositions of them: coherences take
    their filler K reversed (RC is symmetric); compositions are layered with
    the op-lifts of their top arguments; lower-dimensional arguments use the
    lax lifts nat_in. A top-dimensional Y-variable takes down_map[y] : b_y -> a_y
    (a reversed bridge), and has no op-lift without one."""
    Y = frozenset(Y)
    meets = lambda w: bool(fv_tm(w) & Y)
    pmemo = {}
    def plus(x):
        return rename_map(x, plus_map, pmemo)
    _lm = {}
    lax = lambda x: nat_in(H, Y, plus_map, up_map, x, rc, _lm)
    memo = {}
    def go(t):
        hit = memo.get(id(t))
        if hit is not None:
            return hit[1]
        if t[0] == 'v':
            if down_map and t[1] in down_map:
                return down_map[t[1]]
            raise NoFiller('top-dimensional Y-variable has no op-lift')
        Q, B, g = t[1], t[2], t[3]
        Yq = frozenset(q for q in range(len(Q)) if meets(g[q]))
        changed = True
        while changed:
            changed = False
            for q, A_ in enumerate(Q):
                if q not in Yq and A_ != STAR and (fv_ty(A_) & Yq):
                    Yq = Yq | {q}; changed = True
        C, mi, pl, up, K, optops = filler(Q, B, Yq, rc, op=True)
        sub = [None] * len(C)
        for q in range(len(Q)):
            sub[mi[q]] = g[q]
            if q in Yq:
                sub[pl[q]] = plus(g[q])
                sub[up[q]] = go(g[q]) if q in optops else lax(g[q])
        r = subst_tm(K, tuple(sub))
        memo[id(t)] = (t, r)
        return r
    w = go(t)
    a, b = boundary_ab(H, t, meets, lax, plus)
    assert infer(H, w) == arr(infer(H, a), b, a), 'ill-typed op square'
    return w, a, b

def square(H, Y, plus_map, up_map, t, rc):
    """(t↑, a_t, b_t), with the type checked."""
    _lm = {}
    w = nat_in(H, frozenset(Y), plus_map, up_map, t, rc, _lm)
    meets = lambda x: bool(fv_tm(x) & frozenset(Y))
    pmemo = {}
    def plus(x):
        return rename_map(x, plus_map, pmemo)
    a, b = boundary_ab(H, t, meets, lambda x: nat_in(H, frozenset(Y), plus_map, up_map, x, rc, _lm), plus)
    assert infer(H, w) == arr(infer(H, a), a, b), 'ill-typed naturality square'
    return w, a, b

# ---------------------------------------------------------------- event sweep

def _rename_diff(a, b, acc):
    """Collect variable pairs (i, j) where a has i and b has j; False if the
    terms differ in shape."""
    if a == b:
        return True
    if a[0] == 'v' and b[0] == 'v':
        acc.add((a[1], b[1])); return True
    if a[0] != b[0] or a[0] == 'v' or a[1] != b[1] or a[2] != b[2] or len(a[3]) != len(b[3]):
        return False
    return all(_rename_diff(x, y, acc) for x, y in zip(a[3], b[3]))

def _dependents(G, x):
    out = {x}
    for i in range(x + 1, len(G)):
        if fv_ty(G[i]) & out:
            out.add(i)
    return out - {x}

def _vc(G, n, fs):
    w = fs[-1]
    for x in reversed(fs[:-1]):
        w = comp2(G, n - 1, x, w)
    return w

def _is_cap(G, f):
    import rc_heur as Hh
    return Hh.is_identity_value(G, f)

def sweep(G, n, ft, fu, rc):
    """Move one event across a block of caps. ft = [P.., E, c₁⁺..c_r⁺, R..]
    and fu = [P.., c₁..c_r, ...] with cᵢ⁺ = cᵢ[x := x′] and a variable
    e : x -> x′ in G. Returns (W, ft′) with W : vc(ft) -> vc(ft′), where
    ft′ = [P.., c₁..c_r, (τc_r)↑, R..], or None."""
    found = None
    for i in range(len(ft) - 1):
        if _is_cap(G, ft[i]) or not _is_cap(G, ft[i + 1]):
            continue
        for m in range(len(fu)):
            r, pair = 0, None
            while i + 1 + r < len(ft) and m + r < len(fu) and _is_cap(G, ft[i + 1 + r]) and _is_cap(G, fu[m + r]):
                acc = set()
                if not _rename_diff(fu[m + r], ft[i + 1 + r], acc):
                    break
                acc = {p for p in acc if p[0] != p[1]}
                if len(acc) > 1 or (pair is not None and acc and acc != {pair}):
                    break
                if acc:
                    pair = next(iter(acc))
                r += 1
            if r > 0 and pair is not None and (found is None or r > found[2]):
                found = (i, m, r, pair)
        if found is not None:
            break
    if found is None:
        return None
    i, m, r, pair = found
    x, x2 = pair
    es = [k for k, T in enumerate(G) if T != STAR and T[2] == v(x) and T[3] == v(x2)]
    if not es:
        return None
    e = es[0]
    caps = fu[m:m + r]
    dep = _dependents(G, x)
    if any(fv_tm(c) & dep for c in caps):
        return None
    prefix = list(ft[:i])
    rest = list(ft[i + 1 + r:])
    Y, pm, um = {x}, {x: v(x2)}, {x: v(e)}
    plus = lambda c: subst_tm(c, tuple(v(x2) if k == x else v(k) for k in range(len(G))))
    steps = []
    for k, c in enumerate(caps):
        S, a, b = nat_op(G, Y, pm, um, c, rc)
        left = prefix + list(caps[:k])
        right = [plus(cc) for cc in caps[k + 1:]] + rest
        W = S
        if right:
            W = comp2(G, n - 1, W, _vc(G, n, right))
        if left:
            W = comp2(G, n - 1, _vc(G, n, left), W)
        steps.append(W)
    chain = []
    cur = _vc(G, n, ft)
    for W in steps:
        s_ = src(G, W)
        if s_ != cur:
            w = rc(G, infer(G, cur), cur, s_)
            if w is None:
                return None
            chain.append(w)
        chain.append(W)
        cur = tgt(G, W)
    K = chain[0]
    for P_ in chain[1:]:
        K = comp2(G, n, K, P_)
    return K, cur

def sweep_rc(G, A, t, u, rec):
    """rc fallback: slot-normalize both sides, sweep events across cap
    blocks while the factor lists disagree, then compare the rest."""
    import rc_heur as Hh, rc_oracle as R
    n = tdim(A) + 1
    if n < 2:
        return None
    t2, Ct = Hh.slot_norm(G, t, True, rec)
    u2, Cu = Hh.slot_norm(G, u, False, rec)
    ft, fu = R.vfactors(G, t2, n), R.vfactors(G, u2, n)
    try:
        res = sweep(G, n, ft, fu, rec)
    except (NoFiller, TypeError_, AssertionError, KeyError, ValueError):
        return None
    if res is None:
        return None
    W, t3 = res
    pieces = []
    if Ct is not None:
        pieces.append(Ct)
    s0 = _vc(G, n, ft)
    if s0 != t2:
        w = rec(G, A, t2, s0)
        if w is None:
            return None
        pieces.append(w)
    pieces.append(W)
    rest = rec(G, A, t3, u2)
    if rest is None:
        return None
    pieces.append(rest)
    if Cu is not None:
        pieces.append(Cu)
    K = pieces[0]
    for P_ in pieces[1:]:
        K = comp2(G, n, K, P_)
    return K
