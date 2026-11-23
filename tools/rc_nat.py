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
sweep / sweep_rc move an event across a block of caps that differ by one
variable renaming x -> x′ with a context cell x -> x′.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from catt import *

class NoFiller(Exception):
    pass

_K = {}

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
        back[mi[q]] = pl[q]
    def go(t):
        if t[0] == 'v':
            return v(back.get(t[1], t[1]))
        return ('coh', t[1], t[2], tuple(go(u) for u in t[3]))
    return go(t)

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
    K = pieces[0]
    for P_ in pieces[1:]:
        K = comp2(C, n, K, P_)
    return K

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
    def lift(w):
        return nat_in(C, Yimg, {mi[q]: v(pl[q]) for q in Yq}, {mi[q]: v(up[q]) for q in Yq}, w, rc)
    a, b = boundary_ab(C, c, meets, lift, plus)
    A = infer(C, a)
    if comp:
        try:
            w = _layered(Q, B, Yq, C, mi, pl, up, a, b, rc, op)
        except (NoFiller, TypeError_):
            _K[key] = None
            raise NoFiller(key)
    elif op:
        w = rc(C, A, b, a)
    else:
        w = rc(C, A, a, b)
    if w is None:
        _K[key] = None
        raise NoFiller((Q, B, tuple(sorted(Yq))))
    _K[key] = (C, mi, pl, up, w, optops)
    return _K[key]
    

def nat_in(H, Y, plus_map, up_map, t, rc):
    """t↑ in H, for Y ⊆ Var(H) up-closed among the variables t uses,
    with y⁺ = plus_map[y], y↑ = up_map[y]."""
    memo = {}
    def meets(w):
        return bool(fv_tm(w) & Y)
    def plus(w):
        if w[0] == 'v':
            return plus_map.get(w[1], w)
        return ('coh', w[1], w[2], tuple(plus(u) for u in w[3]))
    def lift(w):
        k = w
        if k in memo:
            return memo[k]
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
        memo[k] = r
        return r
    return lift(t)

def nat_op(H, Y, plus_map, up_map, t, rc):
    """The oplax square t↑ᵒᵖ : b_t -> a_t, for t whose top-dimensional
    structure is coherences (caps) and compositions of them: coherences take
    their filler K reversed (RC is symmetric); compositions are layered with
    the op-lifts of their top arguments; lower-dimensional arguments use the
    lax lifts nat_in. A top-dimensional Y-variable has no op-lift."""
    Y = frozenset(Y)
    meets = lambda w: bool(fv_tm(w) & Y)
    def plus(x):
        if x[0] == 'v':
            return plus_map.get(x[1], x)
        return ('coh', x[1], x[2], tuple(plus(u) for u in x[3]))
    lax = lambda x: nat_in(H, Y, plus_map, up_map, x, rc)
    memo = {}
    def go(t):
        if t in memo:
            return memo[t]
        if t[0] == 'v':
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
        memo[t] = r
        return r
    w = go(t)
    a, b = boundary_ab(H, t, meets, lax, plus)
    assert infer(H, w) == arr(infer(H, a), b, a), 'ill-typed op square'
    return w, a, b

def square(H, Y, plus_map, up_map, t, rc):
    """(t↑, a_t, b_t), with the type checked."""
    w = nat_in(H, frozenset(Y), plus_map, up_map, t, rc)
    meets = lambda x: bool(fv_tm(x) & frozenset(Y))
    def plus(x):
        if x[0] == 'v':
            return plus_map.get(x[1], x)
        return ('coh', x[1], x[2], tuple(plus(u) for u in x[3]))
    a, b = boundary_ab(H, t, meets, lambda x: nat_in(H, frozenset(Y), plus_map, up_map, x, rc), plus)
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
