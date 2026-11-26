"""
The top-rank step (h = n) of the relative-coherence descent: r9 Response 3,
"Formal contexts for a change" through "Sorting in a nonglobular lower
skeleton", as one general step. notes/rc-generator.md §4 step 3.

Input: parallel raw rank-n terms t, u : A in G with equal strict value c
whose top chain is nonzero (c is a genuine top cell). The events of c are
the n-variables of its top chain. Each top-cut factor of t and u is
required to carry at most one event (several events in one factor are
split first by rc_heur.split_events; this step does not do it).

The construction, with every same-rank call either a comparison of old
arrows (no events; strict value an identity, h < n) or a comparison of
two single-event factors with the same event:

 1. Canonical events. For an event factor E of the event z : a_z -> b_z,
    take its writing T = src E in the marker context of z (a_z replaced by
    a marker X when it is composite, rc_heur._marker_ctx), and the
    elementary arrow L(T) = T↑ along z at X (rc_nat.nat_in: the depth-zero
    action of T on z). With Q : tgt L(T) -> tgt E (rank n - 1), E is
    compared with L(T) Q (a single-event call). The track becomes
    old blocks and elementary arrows.
 2. Sorting. While t's event order differs from u's, the first event f
    of u that is out of place in t is moved left past its predecessor e
    (they are incomparable, since both orders are linear extensions of the
    precedence of c): with W = L_e(T) B (B the old block between), the
    naturality square of W along f at X_f gives
        W (tgt W)↑ = L_e(T) B L_f(T')  ->  (src W)↑ W⁺ = L_f(T) L_e(T)⁺ B⁺,
    and L_e(T)⁺ is made canonical again by step 1.
 3. Change of writing. With equal orders, u is made canonical the same
    way (comparisons L(S) Q -> E). For the i-th event, with t-state T and
    u-state S, J : S -> T is a rank-(n-1) comparison in the marker context,
    and the square of J along the event gives J L(T) -> L(S) J⁺. The old
    block of t before the event is compared with u's old block followed
    by J (an old call), then the square is applied. The last blocks are
    compared directly.

Every cell is whiskered into the running track, with rebracketings as
single coherences over column contexts (rc_heur.rebracket). Every result
is type-checked by catt.infer; the trusted checker is Agda.

normalize(G, A, t, u, rec) returns w : t -> u or None. `rec` answers the
sub-queries (rank n - 1 comparisons, old-block comparisons, single-event
comparisons, and the naturality fillers of rc_nat).
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from catt import *

STATS = {'split': 0, 'old': 0, 'one': 0, 'low': 0, 'swap': 0, 'square': 0, 'unfold': 0, 'pull': 0}
TRACE = [False]
DUMP = [None]
PUSH = [True]

def _log(*a):
    if TRACE[0]:
        print('rc_events:', *a, flush=True)

class Fail(Exception):
    pass

def _R():
    import rc_oracle
    return rc_oracle

def _H():
    import rc_heur
    return rc_heur

def events(G, f, n):
    return _H()._events(G, f, n)

def vc(G, n, fs):
    return _R().vcomp_over_terms(G, n, fs)

def vc_or_id(G, n, fs, face):
    if not fs:
        return _R().identity(G, face)
    return vc(G, n, fs)

def compose(G, n, cells):
    cells = [c for c in cells if c is not None]
    if not cells:
        return None
    out = cells[0]
    for c in cells[1:]:
        out = comp2(G, n, out, c)
    return out

def rebr(G, n, x, y):
    """x -> y for terms with the same top-cut factors (one coherence over
    the column context), None if x == y; raises Fail otherwise."""
    if x == y:
        return None
    R = _R()
    fx, fy = R.vfactors(G, x, n), R.vfactors(G, y, n)
    if fx != fy:
        if TRACE[0]:
            print('rebr mismatch', len(fx), len(fy), [i for i in range(min(len(fx), len(fy))) if fx[i] != fy[i]][:5], [tdim(infer(G, f)) for f in fx], [tdim(infer(G, f)) for f in fy])
        raise Fail('rebracket: factor lists differ')
    if len(fx) < 2:
        raise Fail('rebracket: single factor')
    return _H().rebracket(G, infer(G, x), x, y)

# ---------------------------------------------------------------- markers

class Marker:
    """The marker context of one event z (rc_heur._marker_ctx), with the
    data of the lift along z: Y = {X}, X⁺ = b_z, X↑ = Z."""
    def __init__(self, G, z):
        H = _H()
        mk = H._marker_ctx(G, z)
        if mk is None:
            raise Fail('no marker context for %d' % z)
        self.G = G
        self.z = z
        self.Gm, self.x, self.zm, self.fwd, self.back = mk
        self.Y = frozenset({self.x})
        self.pmap = {self.x: G[z][3]}
        self.umap = {self.x: v(self.zm)}
        self.rebuild = H._rebuilder(G, self.Gm, {z: v(self.zm)})
        self.memo = {}

    def to_m(self, w):
        """w over the marker context, substituting back to w."""
        wm = self.fwd(w)
        if wm is None:
            wm = self.rebuild(w)
            if wm is None or self.back(wm) != w:
                return None
        return wm

    def lift(self, Tm, rec):
        """L(T) = T↑ along z in the marker context."""
        import rc_nat as N
        try:
            return N.nat_in(self.Gm, self.Y, self.pmap, self.umap, Tm, rec, self.memo)
        except (N.NoFiller, TypeError_, AssertionError, KeyError, ValueError) as e:
            raise Fail('lift: %s' % type(e).__name__)

    def square(self, Jm, rec):
        import rc_nat as N
        try:
            return N.square(self.Gm, self.Y, self.pmap, self.umap, Jm, rec)
        except (N.NoFiller, TypeError_, AssertionError, KeyError, ValueError) as e:
            raise Fail('square: %s' % type(e).__name__)

# ---------------------------------------------------------------- the track

class Track:
    """A running comparison from a fixed start to the current term, which
    is the right-nested composite of `units`. kind[i] is 'old', 'ev'
    (an event factor not yet canonical) or ('L', z, Tm) (the elementary
    arrow L(T) of z, T = back(Tm))."""
    def __init__(self, G, A, n, units, kinds):
        self.G, self.A, self.n = G, A, n
        self.units, self.kinds = list(units), list(kinds)
        self.cur = vc_or_id(G, n, self.units, A[2])
        self.cells = []

    def term(self, units):
        return vc_or_id(self.G, self.n, units, self.A[2])

    def replace(self, i, j, new, new_kinds, cell):
        """Replace units[i:j] (nonempty) by `new` along cell :
        vc(units[i:j]) -> vc(new) (None when equal up to bracketing)."""
        G, n = self.G, self.n
        assert j > i
        if any(x is None for x in new):
            raise Fail('replace: a new unit is None (%s)' % (new_kinds,))
        old = self.units[i:j]
        pre, post = self.units[:i], self.units[j:]
        nxt_units = pre + list(new) + post
        if cell is None:
            target = self.term(nxt_units)
            c = rebr(G, n, self.cur, target)
            if c is not None:
                self.cells.append(c)
            self.cur = target
        else:
            so = vc(G, n, old)
            if src(G, cell) != so and DUMP[0]:
                import pickle
                pickle.dump((G, so, cell, self.kinds[i:j]), open(DUMP[0], 'wb'))
            if src(G, cell) != so:
                cell = compose(G, n, [rebr(G, n, so, src(G, cell)), cell])
            if new and tgt(G, cell) != vc(G, n, new):
                cell = compose(G, n, [cell, rebr(G, n, tgt(G, cell), vc(G, n, new))])
            W = cell
            if post:
                W = comp2(G, n - 1, W, vc(G, n, post))
            if pre:
                W = comp2(G, n - 1, vc(G, n, pre), W)
            c = rebr(G, n, self.cur, src(G, W))
            if c is not None:
                self.cells.append(c)
            self.cells.append(W)
            self.cur = tgt(G, W)
            if not new:
                # remove the identity left by the empty replacement
                if not pre and not post:
                    pass
                elif not post:
                    U = unit_cell(G, n, vc(G, n, pre), False, back=True)
                    self.cells.append(U)
                    self.cur = tgt(G, U)
                else:
                    U = unit_cell(G, n, vc(G, n, post), True, back=True)
                    if pre:
                        U = comp2(G, n - 1, vc(G, n, pre), U)
                    self.cells.append(U)
                    self.cur = tgt(G, U)
        self.units = nxt_units
        self.kinds = self.kinds[:i] + list(new_kinds) + self.kinds[j:]

    def order(self):
        return [k[1] for k in self.kinds if isinstance(k, tuple)]

    def result(self, target):
        c = rebr(self.G, self.n, self.cur, target)
        cells = self.cells + ([c] if c is not None else [])
        return compose(self.G, self.n, cells)

# ---------------------------------------------------------------- the step

class Step:
    def __init__(self, G, A, rec):
        self.G, self.A, self.rec = G, A, rec
        self.n = tdim(A) + 1
        self.mk = {}
        self.query = (None, None)
        self.target_order = []

    def marker(self, z):
        if z not in self.mk:
            self.mk[z] = Marker(self.G, z)
        return self.mk[z]

    def call(self, kind, H, a, b):
        """A recursive comparison a -> b in H (None if equal)."""
        if a == b:
            return None
        STATS[kind] += 1
        _log('call', kind, '|H| =', len(H))
        w = self.rec(H, infer(H, a), a, b)
        if w is None:
            raise Fail('%s call failed' % kind)
        return w

    def canon(self, E, z, reverse=False):
        """For the event factor E of z: (units, kinds, cell) with cell :
        E -> L(T) Q (or L(T) Q -> E when reverse), T = src E."""
        G, n = self.G, self.n
        M = self.marker(z)
        Em = M.to_m(E)
        if Em is None:
            # a top slot holding a composite along n-1 (an old cell before
            # or after the event, so the event's source is not a face of
            # E's head): distribute the head over it first
            r = self.unfold(E, reverse)
            if r is None:
                raise Fail('event factor has no marker form')
            return r
        Tm = src(M.Gm, Em)
        Lm = M.lift(Tm, self.rec)
        kinds = [('L', z, Tm)]
        if Lm == Em:
            return [M.back(Lm)], kinds, None
        Qm = None
        if tgt(M.Gm, Lm) != tgt(M.Gm, Em):
            Qm = self.call('low', M.Gm, tgt(M.Gm, Lm), tgt(M.Gm, Em))
        LQ = Lm if Qm is None else comp2(M.Gm, n - 1, Lm, Qm)
        q = (M.back(LQ), E) if reverse else (E, M.back(LQ))
        if q == self.query or q == self.query[::-1]:
            raise Fail('single-event comparison is the query itself')
        Xm = None
        try:
            Xm = self.head_base(M, Em, Lm, Qm, reverse)
        except Fail as ex:
            _log('head base:', ex)
        if Xm is None:
            Xm = self.call('one', M.Gm, LQ, Em) if reverse else self.call('one', M.Gm, Em, LQ)
        units = [M.back(Lm)] + ([M.back(Qm)] if Qm is not None else [])
        kinds += ['old'] * (len(units) - 1)
        return units, kinds, M.back(Xm)

    def unfold(self, E, reverse):
        """E = H(.., c, ..) with each top-slot argument a composite of k >= 2
        factors along n-1: (units of H(f_1) ... H(f_k), kinds, D), D the
        interchange coherence E -> that (back when reverse); None if E is
        not of that shape."""
        G, n = self.G, self.n
        h2, D = _H().distribute(G, E, not reverse)
        if D is None:
            return None
        units = _R().vfactors(G, h2, n)
        if len(units) < 2:
            return None
        STATS['unfold'] += 1
        _log('unfold into', len(units))
        return units, ['ev' if events(G, x, n) else 'old' for x in units], D

    def head_base(self, M, Em, Lm, Qm, reverse):
        """The single-event comparison Em -> Lm Qm (or back) when Em is a
        composition head H(e) whose pasting context has one top slot,
        holding the event (r9 Response 3, sequentializing: recurse on the
        proper argument e): e -> L_e Q_e by recursion, H(e) -> H(L_e Q_e)
        by top-slot congruence, -> H(L_e) H(Q_e) by distribution, and
        H(L_e) = L(src Em) literally; then H(Q_e) against Qm is an old
        call."""
        Hh = _H()
        G, n = M.Gm, self.n
        if Em[0] != 'coh':
            return None
        _, P, B, sg = Em
        if tdim(B) + 1 != n or ps_dim(P) != n:
            return None
        tops = [i for i, C in enumerate(P) if C != STAR and tdim(C) + 1 == n]
        if len(tops) != 1:
            return None
        i = tops[0]
        em = sg[i]
        if em[0] == 'v':
            return None
        Le = M.lift(src(G, em), self.rec)
        Qe = None
        if tgt(G, Le) != tgt(G, em):
            Qe = self.call('low', G, tgt(G, Le), tgt(G, em))
        LQe = Le if Qe is None else comp2(G, n - 1, Le, Qe)
        cells = []
        h1 = Em
        if LQe != em:
            Xe = self.call('one', G, LQe, em) if reverse else self.call('one', G, em, LQe)
            Cg, h1 = Hh.congruence(G, Em, {i: (LQe, Xe)}, not reverse)
            cells.append(Cg)
        h2 = h1
        if Qe is not None:
            h2, Dc = Hh.distribute(G, h1, not reverse)
            if Dc is None:
                raise Fail('head base: no distribution')
            cells.append(Dc)
        R = _R()
        f2 = R.vfactors(G, h2, n)
        fl = R.vfactors(G, Lm, n)
        if f2[:len(fl)] != fl:
            raise Fail('head base: H(L_e) is not the lift')
        rest = f2[len(fl):]
        face = tgt(G, Lm)
        ro = vc_or_id(G, n, rest, face)
        qo = Qm if Qm is not None else R.identity(G, face)
        if ro != qo:
            X = self.call('old', G, qo, ro) if reverse else self.call('old', G, ro, qo)
            W = comp2(G, n - 1, Lm, X)
            cells.append(W)
        # orient: forward cells run Em -> ... -> Lm Qm; reverse cells were
        # built as their reversals, so they run in the opposite order
        if reverse:
            cells = list(reversed(cells))
            start, end = (Lm if Qm is None else comp2(G, n - 1, Lm, Qm)), Em
        else:
            start, end = Em, (Lm if Qm is None else comp2(G, n - 1, Lm, Qm))
        return chain(G, n, start, cells, end)

    def canonical(self, T):
        """Make every 'ev' unit of the track canonical."""
        while True:
            k = next((i for i, kd in enumerate(T.kinds) if kd == 'ev'), None)
            if k is None:
                return
            E = T.units[k]
            zs = events(self.G, E, self.n)
            if len(zs) != 1:
                units, kinds, cell = self.split(E)
            else:
                units, kinds, cell = self.canon(E, zs[0])
            T.replace(k, k + 1, units, kinds, cell)

    def split(self, E, reverse=False):
        """A factor with several events in the top slots of its head: the
        sequential composite in the target order (rc_heur._split_factor),
        D : E -> seq (or seq -> E when reverse, by the reversed head)."""
        G, n = self.G, self.n
        pos = {z: i for i, z in enumerate(self.target_order)}
        key = lambda c: min((pos.get(z, 10 ** 6), z) for z in events(G, c, n))
        r = _H()._split_factor(G, E, n, key)
        if r is None:
            raise Fail('factor with several events does not split')
        seq, D = r
        if src(G, D) != E:
            # the split's head writes the factor differently (the nested
            # and general splits): glue E to it, by a rebracketing when the
            # top factors agree, else by a comparison
            try:
                g = rebr(G, n, E, src(G, D))
            except Fail:
                g = self.call('split', G, E, src(G, D))
            D = compose(G, n, [g, D])
            if reverse:
                D = self.call('split', G, seq, E)
        elif reverse:
            _, P, B, sg = D
            B2 = arr(B[1], B[3], B[2])
            if side_ok(P, B2[1], B2[2], B2[3]):
                D = ('coh', P, B2, sg)
            else:
                D = self.call('split', G, seq, E)
        units = _R().vfactors(G, seq, n)
        return units, ['ev' if events(G, x, n) else 'old' for x in units], D

    def swap(self, T, p):
        """The elementary arrows at unit positions p < q (consecutive
        events) are swapped by the naturality square of L_e(T) B along f."""
        G, n = self.G, self.n
        lifts = [i for i, kd in enumerate(T.kinds) if isinstance(kd, tuple)]
        q = lifts[lifts.index(p) + 1]
        f = T.kinds[q][1]
        Mf = self.marker(f)
        W = vc(G, n, T.units[p:q])
        Wm = Mf.to_m(W)
        if (Wm is None or Mf.x not in fv_tm(Wm)) and q > p + 1 and not getattr(self, '_pulling', False):
            # f's composite source is written by the old block B after
            # L_e, not by the state before it: move B before L_e (the
            # oplax square of B along e), then swap the bare L_e
            self.pull_back(T, p, q)
            self._pulling = True
            try:
                lifts = [i for i, kd in enumerate(T.kinds) if isinstance(kd, tuple)]
                qf = next(i for i in lifts if T.kinds[i][1] == f)
                return self.swap(T, lifts[lifts.index(qf) - 1])
            finally:
                self._pulling = False
        if Wm is None:
            raise Fail('swap: no marker form of the moving block')
        if Mf.x not in fv_tm(Wm):
            raise Fail('swap: the event source does not occur in the block')
        STATS['swap'] += 1
        sq, a, b = Mf.square(Wm, self.rec)
        sq, a, b = Mf.back(sq), Mf.back(a), Mf.back(b)
        # a = W (tgt W)↑, which must be W L_f(T') up to bracketing
        if Mf.to_m(tgt(G, W)) != T.kinds[q][2]:
            raise Fail('swap: target writing differs from the lift state')
        _log('swap', T.kinds[p][1], f)
        # b = (src W)↑ W⁺ : the new units
        R = _R()
        fb = R.vfactors(G, b, n)
        Lf = Mf.back(Mf.lift(Mf.to_m(src(G, W)), self.rec))
        k = len(R.vfactors(G, Lf, n))
        if fb[:k] != R.vfactors(G, Lf, n):
            raise Fail('swap: square target does not start with the lift')
        rest = R.vfactors(G, vc(G, n, fb[k:]), n)
        new = [Lf]
        kinds = [('L', f, Mf.to_m(src(G, W)))]
        for x in rest:
            zs = events(G, x, n)
            new.append(x)
            kinds.append('ev' if zs else 'old')
        T.replace(p, q + 1, new, kinds, sq)

    def pull_back(self, T, p, q):
        """Units p (the elementary arrow L_e(S)) and p+1..q-1 (an old block
        B): replace L_e(S) B by B⁻ L_e(tgt B⁻) along the oplax square of
        B⁻ along e (rc_nat.nat_op: (src B⁻)↑ B -> B⁻ (tgt B⁻)↑), where B⁻
        is B with e's target b_e written back as e's source (B = (B⁻)⁺)."""
        import rc_nat as N
        from rc_heur import _replace
        G, n = self.G, self.n
        e, Sm = T.kinds[p][1], T.kinds[p][2]
        if any(T.kinds[k] != 'old' for k in range(p + 1, q)):
            raise Fail('pull back: the block is not old')
        Me = self.marker(e)
        B = vc(G, n, T.units[p + 1:q])
        Bm = Me.to_m(B)
        if Bm is None:
            raise Fail('pull back: no marker form of the block')
        be = Me.pmap[Me.x]
        Bm_ = _replace(Bm, be, v(Me.x))
        try:
            infer(Me.Gm, Bm_)
        except (TypeError_, AssertionError, KeyError):
            raise Fail('pull back: the block does not write back')
        if N.rename_map(Bm_, Me.pmap) != Bm or src(Me.Gm, Bm_) != Sm:
            raise Fail('pull back: the block is not the image of its pullback')
        STATS['pull'] += 1
        try:
            sq, a, b = N.nat_op(Me.Gm, Me.Y, Me.pmap, Me.umap, Bm_, self.rec)
        except (N.NoFiller, TypeError_, AssertionError, KeyError, ValueError) as ex:
            raise Fail('pull back: op square: %s' % type(ex).__name__)
        sq = Me.back(sq)
        R = _R()
        Tm2 = tgt(Me.Gm, Bm_)
        L2 = Me.back(Me.lift(Tm2, self.rec))
        new = R.vfactors(G, Me.back(Bm_), n) + [L2]
        kinds = ['old'] * (len(new) - 1) + [('L', e, Tm2)]
        _log('pull back', e, 'across', q - p - 1, 'units')
        T.replace(p, q, new, kinds, sq)

    def back_replace(self, U, i, j, new, new_kinds, cell, back_cells):
        """As Track.replace, for the u side: cell : vc(new) -> vc(units[i:j])
        (towards u), whiskered and recorded in back_cells."""
        G, n = self.G, self.n
        if any(x is None for x in new):
            raise Fail('back_replace: a new unit is None')
        pre, post = U.units[:i], U.units[j:]
        if cell is not None:
            W = cell
            if new and src(G, cell) != vc(G, n, new):
                W = compose(G, n, [rebr(G, n, vc(G, n, new), src(G, cell)), W])
            if post:
                W = comp2(G, n - 1, W, vc(G, n, post))
            if pre:
                W = comp2(G, n - 1, vc(G, n, pre), W)
            back_cells.append(W)
        U.units = pre + list(new) + post
        U.kinds = U.kinds[:i] + list(new_kinds) + U.kinds[j:]

    def push_left(self, Tr, forward, back_cells=None):
        """Move every elementary arrow to the left across the old block
        before it (since the previous event or the start): with W that
        block, the naturality square W L(tgt W) -> L(src W) W⁺ (forward,
        on t) or its oplax form L(src W) W⁺ -> W L(tgt W) (nat_op, on u,
        recorded towards u). The states before the events then are the
        targets of the previous elementary arrows, the same on t and u, and
        the old material collects after the events, renamed by them."""
        import rc_nat as N
        G, n = self.G, self.n
        R = _R()
        e = 0
        while True:
            lifts = [i for i, kd in enumerate(Tr.kinds) if isinstance(kd, tuple)]
            if e >= len(lifts):
                return
            p = lifts[e]
            s0 = lifts[e - 1] + 1 if e else 0
            e += 1
            if p == s0:
                continue
            z, Tm = Tr.kinds[p][1], Tr.kinds[p][2]
            M = self.marker(z)
            W = vc(G, n, Tr.units[s0:p])
            Wm = M.to_m(W)
            if Wm is None or M.x not in fv_tm(Wm) or M.to_m(tgt(G, W)) != Tm:
                _log('push: block has no marker form')
                continue
            Sm = M.to_m(src(G, W))
            if Sm is None:
                continue
            try:
                if forward:
                    STATS['square'] += 1
                    sq, a, b = M.square(Wm, self.rec)
                else:
                    STATS['square'] += 1
                    try:
                        sq, a, b = N.nat_op(M.Gm, M.Y, M.pmap, M.umap, Wm, self.rec)
                    except (N.NoFiller, TypeError_, AssertionError, KeyError, ValueError) as ex:
                        raise Fail('op square: %s' % type(ex).__name__)
                L = M.back(M.lift(Sm, self.rec))
            except Fail as ex:
                _log('push failed:', ex)
                continue
            sq, b = M.back(sq), M.back(b)
            fb, fl = R.vfactors(G, b, n), R.vfactors(G, L, n)
            if fb[:len(fl)] != fl:
                _log('push: square target does not start with the lift')
                continue
            rest = fb[len(fl):]
            new = [L] + rest
            kinds = [('L', z, Sm)] + ['ev' if events(G, x, n) else 'old' for x in rest]
            _log('push', z, 'past', p - s0, 'units')
            if forward:
                Tr.replace(s0, p + 1, new, kinds, sq)
            else:
                self.back_replace(Tr, s0, p + 1, new, kinds, sq, back_cells)

    def sort(self, T, order):
        while True:
            cur = T.order()
            if cur == order:
                return
            i = next(i for i in range(len(order)) if cur[i] != order[i])
            f = order[i]
            j = cur.index(f)
            lifts = [k for k, kd in enumerate(T.kinds) if isinstance(kd, tuple)]
            self.swap(T, lifts[j - 1])
            self.canonical(T)

    def run(self, t, u):
        G, A, n = self.G, self.A, self.n
        R = _R()
        self.query = (t, u)
        ft, fu = R.vfactors(G, t, n), R.vfactors(G, u, n)
        self.target_order = [z for f in fu for z in events(G, f, n)]
        kt = ['ev' if events(G, f, n) else 'old' for f in ft]
        ku = ['ev' if events(G, f, n) else 'old' for f in fu]
        if 'ev' not in kt:
            raise Fail('no events')
        T = Track(G, A, n, ft, kt)
        self.canonical(T)
        # u's canonical form, with the cells pointing towards u
        U = Track(G, A, n, fu, ku)
        back_cells = []
        while True:
            k = next((i for i, kd in enumerate(U.kinds) if kd == 'ev'), None)
            if k is None:
                break
            E = U.units[k]
            zs = events(G, E, n)
            if len(zs) != 1:
                units, kinds, cell = self.split(E, reverse=True)
            else:
                units, kinds, cell = self.canon(E, zs[0], reverse=True)
            self.back_replace(U, k, k + 1, units, kinds, cell, back_cells)
        order = U.order()
        if sorted(order) != sorted(T.order()) or len(set(order)) != len(order):
            raise Fail('event lists differ')
        _log('orders', T.order(), order)
        self.sort(T, order)
        if PUSH[0]:
            self.push_left(T, True)
            self.canonical(T)
            self.push_left(U, False, back_cells)
        # change of writing, event by event
        lt = [i for i, kd in enumerate(T.kinds) if isinstance(kd, tuple)]
        lu = [i for i, kd in enumerate(U.kinds) if isinstance(kd, tuple)]
        for e in range(len(order)):
            lt = [i for i, kd in enumerate(T.kinds) if isinstance(kd, tuple)]
            z = order[e]
            pt, pu = lt[e], lu[e]
            st = (lt[e - 1] + 1) if e else 0
            su = (lu[e - 1] + 1) if e else 0
            M = self.marker(z)
            Tm, Sm = T.kinds[pt][2], U.kinds[pu][2]
            Jm = None
            if Tm != Sm:
                Jm = self.call('low', M.Gm, Sm, Tm)
            J = M.back(Jm) if Jm is not None else None
            bu = U.units[su:pu] + ([J] if J is not None else [])
            bt = T.units[st:pt]
            if any(x is None for x in bt + bu):
                raise Fail('a None unit in the blocks of event %d (t %s, u %s)' % (z, [x is None for x in bt], [x is None for x in bu]))
            face = A[2] if e == 0 else tgt(G, T.units[st - 1])
            if bt != bu:
                X = self.call('old', G, vc_or_id(G, n, bt, face), vc_or_id(G, n, bu, face))
                if bt:
                    T.replace(st, pt, bu, ['old'] * len(bu), X)
                else:
                    # an empty block becomes bu: insert through the unit
                    L = T.units[pt]
                    T.replace(pt, pt + 1, bu + [L], ['old'] * len(bu) + [T.kinds[pt]],
                              compose(G, n, [unit_cell(G, n, L, True), comp2(G, n - 1, X, L) if X is not None else None]))
                lt = [i for i, kd in enumerate(T.kinds) if isinstance(kd, tuple)]
                pt = lt[e]
            if Jm is not None:
                STATS['square'] += 1
                sq, a, b = M.square(Jm, self.rec)
                sq = M.back(sq)
                Ls = U.units[pu]
                Jp = M.back(rename_plus(M, Jm))
                T.replace(pt - 1, pt + 1, [Ls, Jp], [U.kinds[pu], 'old'], sq)
        # the last block
        lt = [i for i, kd in enumerate(T.kinds) if isinstance(kd, tuple)]
        st, su = lt[-1] + 1, lu[-1] + 1
        bt, bu = T.units[st:], U.units[su:]
        if bt != bu:
            face = tgt(G, T.units[st - 1])
            X = self.call('old', G, vc_or_id(G, n, bt, face), vc_or_id(G, n, bu, face))
            if bt:
                T.replace(st, len(T.units), bu, ['old'] * len(bu), X)
            else:
                L = T.units[st - 1]
                T.replace(st - 1, st, [L] + bu, [T.kinds[st - 1]] + ['old'] * len(bu),
                          compose(G, n, [unit_cell(G, n, L, False), comp2(G, n - 1, L, X) if X is not None else None]))
        if T.units != U.units:
            raise Fail('tracks differ after normalization')
        # back_cells were collected left to right on u; each goes from a
        # more canonical u to the previous one, so they apply in reverse
        w = chain(G, n, t, T.cells + list(reversed(back_cells)), u)
        if w is None:
            return R.identity(G, t)
        return w

def unit_cell(G, n, x, left, back=False):
    """x -> 1 x (left) or x -> x 1, x an n-cell, 1 the identity on its
    (n-1)-source or target: one coherence over the n-disc (reversed when
    back)."""
    import rc_descent as D
    R = _R()
    def one(P, xs):
        y = xs[0]
        if left:
            return comp2(P, n - 1, R.identity(P, src(P, y)), y)
        return comp2(P, n - 1, y, R.identity(P, tgt(P, y)))
    l, r = (lambda P, xs: xs[0]), one
    if back:
        l, r = r, l
    return D._gcoh(G, 0, [n], [x], l, r)

def chain(G, n, start, cells, end):
    """Compose cells from start to end, gluing consecutive ends that
    differ only in bracketing."""
    out, cur = [], start
    for c in cells:
        if c is None:
            continue
        out.append(rebr(G, n, cur, src(G, c)))
        out.append(c)
        cur = tgt(G, c)
    out.append(rebr(G, n, cur, end))
    return compose(G, n, out)

def rename_plus(M, Jm):
    import rc_nat as N
    return N.rename_map(Jm, M.pmap)

DEPTH = [0]
MAX_DEPTH = [4]
FAILS = [None]    # a list to collect the failed (G, A, t, u) in, for debugging

def normalize(G, A, t, u, rec):
    n = tdim(A) + 1
    if n < 2 or t == u or DEPTH[0] >= MAX_DEPTH[0]:
        return None
    if _R().strict_image(G, t) != _R().strict_image(G, u):
        return None
    DEPTH[0] += 1
    try:
        S = Step(G, A, rec)
        w = S.run(t, u)
    except (Fail, TypeError_, TypeError, AssertionError, KeyError, ValueError, StopIteration) as e:
        _log('fail:', type(e).__name__, e)
        if TRACE[0] and not isinstance(e, Fail) or 'rebracket' in str(e):
            import traceback
            if TRACE[0]:
                traceback.print_exc()
        if FAILS[0] is not None:
            FAILS[0].append(((G, A, t, u), str(e)))
        return None
    finally:
        DEPTH[0] -= 1
    if w is None or infer(G, w) != arr(A, t, u):
        _log('fail: ill-typed result')
        return None
    return w
