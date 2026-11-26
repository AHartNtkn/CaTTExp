"""
A sharing-preserving Python mirror of CaTTExp.ConeRC.ConeGenS (cones over
coherence terms from a relative-coherence oracle), for driving the oracle
loop on cones whose Agda evaluation is too slow.

Why: the Agda construction evaluates `tyE`, `ev` and `==Tm` on expression
trees with no memo, and `tyF` on a binary composite recurses into both
factors and then into the composite of their faces, so its cost grows
exponentially with the nesting depth of the transports. On the Horiz3 cone
the compiled driver took 14 min for round 23, 85 min for round 24 and over
55 min (stopped) for round 25. Here every expression is hash-consed and
`tyE` / `ev` are memoized per node, and terms are built with catt.mk_coh,
so the same construction runs in polynomial time.

Trust: none. This file only computes the next oracle query. It mirrors the
Agda definitions clause by clause (names kept), and `check_against`
compares its queries with the ones the Agda driver printed for the rounds
it finished. The cone is meant to be certified in Agda (a DAG certificate
of the context, then tied to `ConeRCS.cone`); for Horiz3 neither is done
yet.

Covered: the expression constructors the cone construction and the
three-dimensional shapes use (v, bn, idn, raw). Fuel: the Agda functions
take fuel, which is not modelled here except in P, where it is cheap and
exact. On Horiz3 it is checked not to run out: the depth Agda's fuelled
tyF / evF / evTyF need is at most 52, against fuelOf K >= 81 (measured in
the review of PR #636). For another shape, check this again.

Usage:
  import cone_rcs as C
  q = C.first_miss(C.HORIZ3, oracle)   # oracle(G, A, t, u) -> Tm or None
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import catt
from catt import STAR, arr, v as tv, tree_ctx, disc_tree, glue_tree, subst_ty

sys.setrecursionlimit(1000000)

# ---------------------------------------------------------------- expressions
# Ex   : ('v', i) | ('bn', k, a, b) | ('idn', e) | ('raw', w, a, b)
# ExTy : ('ob',) | ('hom', A, s, t)
# Every node is interned, so equal expressions are the same object and the
# memos below can key on id().

_IX = {}

def _intern(key, make):
    r = _IX.get(key)
    if r is None:
        r = make()
        _IX[key] = r
    return r

def ev_(i):
    return _intern(('v', i), lambda: ('v', i))

def bn(k, a, b):
    return _intern(('bn', k, id(a), id(b)), lambda: ('bn', k, a, b))

def idn(e):
    return _intern(('idn', id(e)), lambda: ('idn', e))

def raw(w, a, b):
    return _intern(('raw', id(w), id(a), id(b)), lambda: ('raw', w, a, b))

OB = ('ob',)

def hom(A, s, t):
    return _intern(('hom', id(A), id(s), id(t)), lambda: ('hom', A, s, t))

def dimE(A):
    n = 0
    while A[0] == 'hom':
        n += 1; A = A[1]
    return n

def srcE(A):
    return A[2] if A[0] == 'hom' else ev_(0)

def tgtE(A):
    return A[3] if A[0] == 'hom' else ev_(0)

def baseE(A):
    return A[1] if A[0] == 'hom' else OB

# ---------------------------------------------------------------- Cones layer 1 (cells)
# Cell = (Tm, Ty)

def dimC(c):
    return catt.tdim(c[1]) + 1

def srcC(c):
    t, A = c
    return (A[2], A[1]) if A != STAR else (t, STAR)

def tgtC(c):
    t, A = c
    return (A[3], A[1]) if A != STAR else (t, STAR)

def diskGo(n, c):
    out = []
    def go(n, c):
        if n == 0:
            out.append(c[0]); return
        go(n - 1, srcC(c))
        out.append(tgtC(c)[0]); out.append(c[0])
    go(n, c)
    return out

def diskList(c):
    return diskGo(dimC(c), c)

def restGo(k, n, c):
    if n == 0:
        return []
    if dimC(c) == k:
        return []
    return restGo(k, n - 1, srcC(c)) + [tgtC(c)[0], c[0]]

def restDisk(k, c):
    return restGo(k, dimC(c), c)

def lookupTy(G, i):
    return G[i] if 0 <= i < len(G) else STAR

def gen(G, i):
    return (tv(i), lookupTy(G, i))

_DISK = {}
def Disk(n):
    r = _DISK.get(n)
    if r is None:
        r = _DISK[n] = tree_ctx(disc_tree(n))
    return r

def idC(c):
    n = dimC(c)
    D = Disk(n)
    A = arr(lookupTy(D, 2 * n), tv(2 * n), tv(2 * n))
    return (catt.mk_coh(D, A, tuple(diskList(c))), arr(c[1], c[0], c[0]))

_BINHEAD = {}
def _bin_head(k, p, q):
    """(P, A) of binF k on cells of dimensions p, q: they depend only on
    (k, p, q) (gu, gw are generic cells of P)."""
    key = (k, p, q)
    r = _BINHEAD.get(key)
    if r is not None:
        return r
    P = tree_ctx(glue_tree(p, k, q))
    rr = max(p, q)
    gu = gen(P, p + p)
    gw = gen(P, len(P) - 1)
    lo = lambda c: c if dimC(c) < rr else srcC(c)
    hi = lambda c: c if dimC(c) < rr else tgtC(c)
    if rr == k + 1:
        A = arr(srcC(gu)[1], srcC(gu)[0], tgtC(gw)[0])
    else:
        s1 = binC(k, lo(gu), lo(gw))
        t1 = binC(k, hi(gu), hi(gw))
        A = arr(s1[1], s1[0], t1[0])
    r = _BINHEAD[key] = (P, A)
    return r

def binC(k, u, w):
    p, q = dimC(u), dimC(w)
    P, A = _bin_head(k, p, q)
    sig = tuple(diskList(u) + restDisk(k, w))
    return (catt.mk_coh(P, A, sig), subst_ty(A, sig))

# ---------------------------------------------------------------- tyE / ev

class Ctx:
    """An ExCtx that only grows (as in ConeGenS.build); memos are kept per
    context object and stay valid under appending, since a node's type
    only depends on the entries of the variables it mentions."""
    def __init__(self, tys):
        self.tys = list(tys)
        self._ty = {}
        self._ev = {}
        self._evty = {}

    def append(self, A):
        self.tys.append(A)

    def tyE(self, e):
        r = self._ty.get(id(e))
        if r is not None:
            return r
        r = self._tyF(e)
        self._ty[id(e)] = r
        return r

    def _tyF(self, e):
        tag = e[0]
        if tag == 'v':
            i = e[1]
            if i >= len(self.tys):
                # Agda gives ob here and recomputes at a larger K; a memo
                # would go stale, so fail loudly instead (never happens on
                # a well-formed diagram: projections refer to earlier entries)
                raise IndexError('cone_rcs: variable %d outside the context' % i)
            return self.tys[i]
        if tag == 'idn':
            return hom(self.tyE(e[1]), e[1], e[1])
        if tag == 'raw':
            return hom(self.tyE(e[2]), e[2], e[3])
        if tag == 'bn':
            k, u, w = e[1], e[2], e[3]
            A = self.tyE(u); B = self.tyE(w)
            r = max(dimE(A), dimE(B))
            if r == k + 1:
                return hom(baseE(A), srcE(A), tgtE(B))
            lo = lambda C, x: x if dimE(C) < r else srcE(C)
            hi = lambda C, x: x if dimE(C) < r else tgtE(C)
            s1 = bn(k, lo(A, u), lo(B, w))
            t1 = bn(k, hi(A, u), hi(B, w))
            return hom(self.tyE(s1), s1, t1)
        raise NotImplementedError('tyE: ' + tag)

    def ev(self, e):
        r = self._ev.get(id(e))
        if r is not None:
            return r
        tag = e[0]
        if tag == 'v':
            r = tv(e[1])
        elif tag == 'raw':
            r = e[1]
        elif tag == 'idn':
            r = idC(self.cell(e[1]))[0]
        elif tag == 'bn':
            r = binC(e[1], self.cell(e[2]), self.cell(e[3]))[0]
        else:
            raise NotImplementedError('ev: ' + tag)
        self._ev[id(e)] = r
        return r

    def evTy(self, A):
        r = self._evty.get(id(A))
        if r is not None:
            return r
        r = STAR if A[0] == 'ob' else arr(self.evTy(A[1]), self.ev(A[2]), self.ev(A[3]))
        self._evty[id(A)] = r
        return r

    def cell(self, e):
        return (self.ev(e), self.evTy(self.tyE(e)))

    def evCtx(self):
        return tuple(self.evTy(A) for A in self.tys)

# ---------------------------------------------------------------- rc1 (GraphFillerTotal)

def vtx(i):
    return 0 if i == 0 else 2 * i - 1

def edge(i):
    return 2 * i

def path(t):
    if t[0] == 'v':
        return [t[1]]
    return pathCh(t[3])

def pathCh(s):
    out = []
    # pathCh (τ ,ₛ _ ,ₛ e) = pathCh τ ++ path e, peeled from the right
    n = len(s)
    ends = []
    while n >= 2:
        ends.append(s[n - 1]); n -= 2
    for e in reversed(ends):
        out += path(e)
    return out

def lift(t, o):
    if t[0] == 'v':
        return tv(edge(o + 1))
    return catt.mk_coh(t[1], t[2], liftCh(t[3], o))

def liftCh(s, o):
    if len(s) == 0:
        return ()
    if len(s) == 1:
        return (tv(vtx(o)),)
    tau, e = s[:-2], s[-1]
    pt = len(pathCh(tau))
    return liftCh(tau, o) + (tv(vtx(len(path(e)) + pt + o)), lift(e, pt + o))

def tgtOf(G, e):
    A = G[e] if 0 <= e < len(G) else None
    if A is not None and A != STAR and A[3][0] == 'v':
        return A[3][1]
    return 0

def wsub(G, a, p):
    out = [tv(a)]
    x = a
    for e in p:
        x = tgtOf(G, e)
        out += [tv(x), tv(e)]
    return tuple(out)

_CHAIN = {}
def chainC(k):
    r = _CHAIN.get(k)
    if r is None:
        G = [STAR]
        for j in range(k):
            G += [STAR, arr(STAR, tv(vtx(j)), tv(vtx(j + 1)))]
        r = _CHAIN[k] = tuple(G)
    return r

def rc1(G, A, t, u):
    if A == STAR or A[1] != STAR or A[2][0] != 'v':
        return None
    if path(t) != path(u):
        return None
    pu = path(t)
    n = len(pu)
    B = arr(arr(STAR, tv(0), tv(vtx(n))), lift(t, 0), lift(u, 0))
    return catt.mk_coh(chainC(n), B, wsub(G, A[2][1], pu))

# ---------------------------------------------------------------- ConeGenS

class Miss(Exception):
    def __init__(self, q):
        self.q = q

class Fail(Exception):
    pass

FUEL = 64

class ConeGenS:
    def __init__(self, split, Gamma, oracle):
        self.split = split
        self.Gamma = list(Gamma)
        self.n = len(Gamma)
        self.c = ev_(self.n)
        self.oracle = oracle

    def pr(self, i):
        return ev_(self.n + 1 + i)

    # --- At K
    def dimK(self, e):
        return dimE(self.K.tyE(e))

    def sE(self, e):
        return srcE(self.K.tyE(e))

    def tE(self, e):
        return tgtE(self.K.tyE(e))

    def iter_s(self, k, e):
        for _ in range(k):
            e = self.sE(e)
        return e

    def face(self, b, r, e):
        d = self.dimK(e)
        if r < d:
            return self.iter_s(d - r, e) if b else self.tE(self.iter_s(d - (r + 1), e))
        return e

    def eq(self, a, b):
        return a is b or self.K.ev(a) == self.K.ev(b)

    def fillE(self, a, b):
        K = self.K
        G = K.evCtx()
        A = K.evTy(K.tyE(a))
        t, u = K.ev(a), K.ev(b)
        w = self.oracle(G, A, t, u)
        if w is None:
            raise Miss((G, A, t, u))
        return raw(w, a, b)

    def fixS(self, r, L, W):
        fW = self.face(True, r, W)
        if self.eq(L, fW):
            return W
        return bn(r, self.fillE(L, fW), W)

    def fixT(self, r, W, R):
        fW = self.face(False, r, W)
        if self.eq(fW, R):
            return W
        return bn(r, W, self.fillE(fW, R))

    def transport(self, m, L, R, W):
        for r in range(1, m + 1):
            W = self.fixS(r, L(r), W)
            W = self.fixT(r, W, R(r))
        return W

    def compose(self, j, X, Y):
        if j == 0:
            return bn(0, X, Y)
        jj = j - 1
        Y1 = self.transport(jj, lambda r: self.face(True, r, X), lambda r: self.face(False, r, X), Y)
        Y2 = self.fixS(j, self.face(False, j, X), Y1)
        return bn(j, X, Y2)

    def nz(self, e):
        if e[0] == 'v':
            return True
        if e[0] == 'bn':
            d = self.dimK(e)
            a, b = e[2], e[3]
            return (self.dimK(a) == d and self.nz(a)) or (self.dimK(b) == d and self.nz(b))
        return False

    def P(self, f, u):
        if f == 0:
            raise Fail()
        if u[0] == 'v':
            return self.pr(u[1])
        f -= 1
        if self.nz(u):
            return self.liftG(True, f, u)
        Pt = self.P(f, self.tE(u))
        Tu = self.Tc(f, u)
        return self.fillE(Pt, Tu)

    def Ps(self, f, u):
        if f == 0:
            raise Fail()
        if u[0] == 'v':
            return self.pr(u[1])
        if self.split and self.nz(u):
            return self.liftG(False, f - 1, u)
        return self.P(f, u)

    def liftG(self, full, f, u):
        if u[0] != 'bn':
            raise Fail()
        k, a, b = u[1], u[2], u[3]
        m = self.dimK(u)
        top = m if full else max(m - 1, 0)
        if self.split and (k + 1 < self.dimK(a)) and (k + 1 < self.dimK(b)):
            u1 = bn(k + 1, bn(k, a, self.face(True, k + 1, b)), bn(k, self.face(False, k + 1, a), b))
            u2 = self.transport(max(m - 1, 0), lambda r: self.face(True, r, u), lambda r: self.face(False, r, u), u1)
            w = self.fillE(u2, u)
            Pu1 = self.P(f, u2)
            Rw = self.R(f, m, w)
            Pt = self.P(f, self.tE(u))
            Tu = self.Tc(f, u)
            return self.transport(m, lambda r: Pt if r == m else self.face(True, r, Pt),
                                  lambda r: Tu if r == m else self.face(False, r, Pt), bn(m, Pu1, Rw))
        Pa = self.Ps(f, a)
        Pb = self.Ps(f, b)
        Rb = self.R(f, k, self.face(False, k + 1, b))
        X = self.compose(k, Pa, Rb)
        W0 = self.compose(k + 1, Pb, X)
        Pt = self.P(f, self.tE(u))
        Tu = self.Tc(f, u)
        return self.transport(top, lambda r: Pt if r == m else self.face(True, r, Pt),
                              lambda r: Tu if r == m else self.face(False, r, Pt), W0)

    def R(self, f, j, w):
        if j == 0:
            return w
        p = self.P(f, self.face(True, j - 1, w))
        r = self.R(f, j - 1, w)
        return bn(j - 1, p, r)

    def Tc(self, f, u):
        return self.R(f, self.dimK(u), u)

    def projTy(self, x, A):
        if A[0] == 'ob':
            return hom(OB, self.c, ev_(x))
        pt = self.P(FUEL, A[3])
        l = self.Tc(FUEL, ev_(x))
        return hom(self.K.tyE(pt), pt, l)

    def build(self):
        self.K = Ctx(self.Gamma + [OB])
        for x, A in enumerate(self.Gamma):
            B = self.projTy(x, A)
            self.K.append(B)
        return self.K

def cone_out(Gamma, oracle, split=True):
    """('ret', K) | ('miss', query) | ('fail',)"""
    g = ConeGenS(split, Gamma, oracle)
    try:
        return ('ret', g.build())
    except Miss as m:
        return ('miss', m.q)
    except Fail:
        return ('fail',)

def first_miss(Gamma, oracle, split=True):
    o = cone_out(Gamma, oracle, split)
    return o[1] if o[0] == 'miss' else None

# ---------------------------------------------------------------- shapes

def diskTy(j):
    A = OB
    for i in range(j):
        A = hom(A, ev_(i + i), ev_(i + i + 1))
    return A

def DiskEx(n):
    out = []
    for j in range(n):
        out += [diskTy(j), diskTy(j)]
    return out + [diskTy(n)]

def _horiz3():
    V = ev_
    H2 = hom(hom(OB, V(0), V(7)), bn(0, V(2), V(8)), bn(0, V(3), V(9)))
    h1 = hom(OB, V(1), V(7))
    h2 = hom(h1, V(8), V(9))
    return DiskEx(3) + [OB, h1, h1, h2, h2, hom(h2, V(10), V(11)),
                        hom(H2, bn(0, V(4), V(10)), bn(0, V(5), V(11))),
                        hom(hom(H2, bn(0, V(4), V(10)), bn(0, V(5), V(11))), bn(0, V(6), V(12)), V(13))]

HORIZ3 = _horiz3()
