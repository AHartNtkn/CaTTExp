"""
A small CaTT kernel in Python, mirroring src/CaTTExp/Syntax.agda:
de Bruijn levels, coh over pasting contexts, syntactic equality.

Used only to *generate* terms; the Agda checker (CaTTExp.Check) is the
authority. Everything generated here is also re-checked by `infer`
below before it is emitted.

Ty  : ('*',) | ('->', A, s, t)
Tm  : ('v', i) | ('coh', P, A, sub)      P a ctx (tuple of Ty), sub a tuple of Tm
Ctx : tuple of Ty
"""
from functools import lru_cache
import sys
sys.setrecursionlimit(100000)

STAR = ('*',)

def arr(A, s, t):
    return ('->', A, s, t)

def v(i):
    return ('v', i)

# ---------------------------------------------------------------- basics

@lru_cache(maxsize=300000)
def tdim(A):
    return -1 if A == STAR else tdim(A[1]) + 1

def id_memo(f):
    """Memoize f on the identities of its arguments (checked on a hit):
    hashing a term walks its shared subterms as a tree, which is exponential
    for the deeply shared terms the oracle builds. Bounded by clearing."""
    memo = {}
    def g(*args):
        key = tuple(map(id, args))
        hit = memo.get(key)
        if hit is not None and all(a is b for a, b in zip(hit[0], args)):
            return hit[1]
        r = f(*args)
        if len(memo) > 100000:
            memo.clear()
        memo[key] = (args, r)
        return r
    g.cache_clear = memo.clear
    g.__wrapped__ = f
    return g

def subst_tm(t, s, _m=None):
    # memoized by identity within one call: shared subterms stay shared
    if t[0] == 'v':
        return s[t[1]]
    if _m is None:
        _m = {}
    k = id(t)
    hit = _m.get(k)
    if hit is not None and hit[0] is t:
        return hit[1]
    r = ('coh', t[1], t[2], tuple(subst_tm(u, s, _m) for u in t[3]))
    _m[k] = (t, r)
    return r

def subst_ty(A, s, _m=None):
    if A == STAR:
        return A
    if _m is None:
        _m = {}
    return ('->', subst_ty(A[1], s, _m), subst_tm(A[2], s, _m), subst_tm(A[3], s, _m))

@id_memo
def fv_tm(t):
    if t[0] == 'v':
        return frozenset([t[1]])
    r = frozenset()
    for u in t[3]:
        r |= fv_tm(u)
    return r

@id_memo
def fv_ty(A):
    if A == STAR:
        return frozenset()
    return fv_ty(A[1]) | fv_tm(A[2]) | fv_tm(A[3])

# ---------------------------------------------------------------- pasting contexts from trees

def tree_ctx(tree):
    """tree: tuple of child trees. Returns ctx (tuple of Ty), same order as Agda's psOf."""
    ctx = [STAR]
    def emit(node, cur, A):
        for child in node:
            y = len(ctx); ctx.append(A)
            f = len(ctx); ctx.append(arr(A, v(cur), v(y)))
            emit(child, f, arr(A, v(cur), v(y)))
            cur = y
    emit(tree, 0, STAR)
    return tuple(ctx)

def disc_tree(n):
    t = ()
    for _ in range(n):
        t = (t,)
    return t

def chain_tree(k):
    return tuple(() for _ in range(k))

def ps_dim(P):
    return max(tdim(A) + 1 for A in P)

@lru_cache(maxsize=100000)
def ps_boundary_vars(P, k, sign):
    """Variables of the k-boundary of ps P (sign '-' or '+'), a frozenset."""
    return frozenset(_ps_boundary_vars(P, k, sign))

def _ps_boundary_vars(P, k, sign):
    S = set()
    for i, A in enumerate(P):
        d = tdim(A) + 1
        if d < k:
            S.add(i)
        elif d == k:
            # excluded if it is the target (for '-') / source (for '+') of a (k+1)-var
            bad = False
            for j, B in enumerate(P):
                if tdim(B) + 1 == k + 1:
                    if sign == '-' and B[3] == v(i): bad = True
                    if sign == '+' and B[2] == v(i): bad = True
            if not bad:
                S.add(i)
    return S

def restrict(P, S):
    """Restrict ctx P to down-closed var set S; return (ctx, incl) with incl the
    substitution P|S -> P (list of terms in P indexed by new levels)."""
    order = sorted(S)
    ren = {old: new for new, old in enumerate(order)}
    rs = [None] * len(P)
    for old in order:
        rs[old] = v(ren[old])
    def ren_tm(t):
        if t[0] == 'v': return v(ren[t[1]])
        return ('coh', t[1], t[2], tuple(ren_tm(u) for u in t[3]))
    def ren_ty(A):
        if A == STAR: return A
        return ('->', ren_ty(A[1]), ren_tm(A[2]), ren_tm(A[3]))
    ctx = tuple(ren_ty(P[o]) for o in order)
    incl = tuple(v(o) for o in order)
    return ctx, incl

# ---------------------------------------------------------------- typing

class TypeError_(Exception):
    pass

@lru_cache(maxsize=None)
def is_ps(P):
    # Rebuild from depths, as the Agda checker does.
    try:
        t = tree_of(P)
    except Exception:
        return False
    return t is not None and tree_ctx(t) == P

def tree_of(P):
    if not P or P[0] != STAR: return None
    rest = P[1:]
    if len(rest) % 2: return None
    depths = [tdim(rest[2*i+1]) + 1 for i in range(len(rest)//2)]
    def forest(lvl, ds):
        out = []
        while ds and ds[0] == lvl:
            cs, ds = forest(lvl + 1, ds[1:])
            out.append(tuple(cs))
        if ds and ds[0] > lvl:
            raise ValueError
        return out, ds
    ts, r = forest(1, depths)
    if r: return None
    return tuple(ts)

def side_ok(P, A, t, u):
    full = set(range(len(P)))
    vt = set(fv_tm(t)) | set(fv_ty(A))
    vu = set(fv_tm(u)) | set(fv_ty(A))
    if vt == full and vu == full:
        return True
    n = ps_dim(P)
    if n == 0:
        return False
    return vt == ps_boundary_vars(P, n - 1, '-') and vu == ps_boundary_vars(P, n - 1, '+')

_IDC = {}   # id(G) -> (G, {id(t): (t, type)}): identity-keyed memo, so that
            # large shared terms are not rehashed at every subterm

_IDN = [0]

def infer(G, t, _cache={}):
    g = _IDC.get(id(G))
    if g is None or g[0] is not G:
        g = (G, {}, {})
        _IDC[id(G)] = g
    hit = g[1].get(id(t))
    if hit is not None and hit[0] is t:
        return hit[1]
    if t[0] == 'coh':
        # structural memo: equal terms rebuilt as new tuples (substitution,
        # composition) are checked once per context
        # keyed by the identities of the head and the arguments (hashing
        # the term itself would walk its shared subterms as a tree)
        key = (id(t[1]), id(t[2])) + tuple(map(id, t[3]))
        h2 = g[2].get(key)
        if h2 is not None and h2[0][1] is t[1] and h2[0][2] is t[2] and all(
                a is b for a, b in zip(h2[0][3], t[3])):
            r = h2[1]
        else:
            r = _infer(G, t, _cache)
            g[2][key] = (t, r)
    else:
        r = _infer(G, t, _cache)
    g[1][id(t)] = (t, r)
    _IDN[0] += 1
    if _IDN[0] > 400000:          # the memo keeps its terms alive: bound it
        _IDC.clear()
        _IDN[0] = 0
    return r

def _infer(G, t, _cache):
    if t[0] == 'v':
        if t[1] >= len(G): raise TypeError_('var out of range')
        r = G[t[1]]
    else:
        _, P, A, s = t
        if A == STAR: raise TypeError_('coh at *')
        _head_ok(P, A)
        if len(s) != len(P): raise TypeError_('sub length')
        for i, (Bi, ti) in enumerate(zip(P, s)):
            if infer(G, ti) != subst_ty(Bi, s):
                raise TypeError_('sub entry %d ill-typed' % i)
        r = subst_ty(A, s)
    return r

@lru_cache(maxsize=200000)
def _head_ok(P, A):
    """The coherence head coh_P(A) is well formed (independent of the
    substitution, so cached)."""
    if not is_ps(P): raise TypeError_('not ps')
    check_ty_cached(P, A)
    if not side_ok(P, A[1], A[2], A[3]):
        raise TypeError_('side condition fails')
    return True

@lru_cache(maxsize=300000)
def check_ty_cached(G, A):
    if A == STAR: return True
    check_ty_cached(G, A[1])
    if infer(G, A[2]) != A[1] or infer(G, A[3]) != A[1]:
        raise TypeError_('ill-formed arrow type')
    return True

def check_ctx(G):
    for i, A in enumerate(G):
        check_ty_cached(G[:i], A)

# ---------------------------------------------------------------- substitutions by unification

def sub_from(P, G, images):
    """images: dict var-of-P -> term-in-G for some vars; extend by unifying types."""
    s = dict(images)
    changed = True
    while changed:
        changed = False
        for i in sorted(s.keys(), reverse=True):
            A = P[i]
            if A == STAR: continue
            B = infer(G, s[i])
            def unify(A, B):
                nonlocal changed
                if A == STAR: return
                for pa, pb in ((A[2], B[2]), (A[3], B[3])):
                    j = pa[1]
                    if j in s:
                        if s[j] != pb: raise TypeError_('unify clash at %d' % j)
                    else:
                        s[j] = pb; changed = True
                unify(A[1], B[1])
            unify(A, B)
    if len(s) != len(P):
        raise TypeError_('substitution underdetermined')
    return tuple(s[i] for i in range(len(P)))

def maximal_vars(P):
    used = set()
    for A in P:
        if A != STAR:
            used.add(A[2][1]); used.add(A[3][1])
    return [i for i in range(len(P)) if i not in used]

# ---------------------------------------------------------------- unbiased composites

@lru_cache(maxsize=None)
def ucomp(P):
    """Unbiased composite of ps P, as a term over P (BMOSV Def 2.1)."""
    n = ps_dim(P)
    mx = maximal_vars(P)
    if len(mx) == 1 and tdim(P[mx[0]]) + 1 == n:
        return v(mx[0])
    if n == 0:
        return v(0)
    lo, li = restrict(P, ps_boundary_vars(P, n - 1, '-'))
    hi, hj = restrict(P, ps_boundary_vars(P, n - 1, '+'))
    s_ = subst_tm(ucomp(lo), li)
    t_ = subst_tm(ucomp(hi), hj)
    A = infer(P, s_)
    return ('coh', P, arr(A, s_, t_), tuple(v(i) for i in range(len(P))))

def comp_tree(tree, G, maxims):
    """Unbiased composite of the ps of `tree`, with its maximal variables
    (in order) sent to the terms `maxims` of G."""
    P = tree_ctx(tree)
    mx = maximal_vars(P)
    assert len(mx) == len(maxims), (len(mx), len(maxims))
    s = sub_from(P, G, dict(zip(mx, maxims)))
    return subst_tm(ucomp(P), s)

def tdim_tm(G, t):
    """Dimension of `t`, computed structurally.  For a coherence
    ('coh', P, A, s) the arrow depth of subst_ty(A, s) is that of A, so the
    dimension needs neither type inference nor a walk of the substitution:
    inferring it walks the whole term, which is the dominant cost (and, with
    the memo holding substituted types alive, the dominant memory use) when
    the oracle composes deeply shared terms."""
    if t[0] == 'v':
        return tdim(G[t[1]]) + 1
    return tdim(t[2]) + 1

def glue_tree(p, k, q):
    """D^p glued to D^q along a k-disc (k < p, q)."""
    a = disc_tree(p - k - 1)
    b = disc_tree(q - k - 1)
    t = (a, b)
    for _ in range(k):
        t = (t,)
    return t

def comp2(G, k, a, b):
    """Binary composite a *_k b (whiskering when dims differ)."""
    p, q = tdim_tm(G, a), tdim_tm(G, b)
    return comp_tree(glue_tree(p, k, q), G, [a, b])

def coh_between(G, tree, maxims, src_over_P, tgt_over_P):
    """coh over ps(tree) with type src -> tgt (terms over P), instantiated."""
    P = tree_ctx(tree)
    mx = maximal_vars(P)
    s = sub_from(P, G, dict(zip(mx, maxims)))
    A = infer(P, src_over_P)
    assert A == infer(P, tgt_over_P), 'not parallel'
    return ('coh', P, arr(A, src_over_P, tgt_over_P), s)

def src(G, t): return infer(G, t)[2]
def tgt(G, t): return infer(G, t)[3]

# ---------------------------------------------------------------- Agda output

def agda_tm(t):
    if t[0] == 'v':
        return '(v %d)' % t[1]
    return '(coh %s %s %s)' % (ctx_name(t[1]), agda_ty(t[2]), agda_sub(t[3]))

def agda_ty(A):
    if A == STAR: return '⋆'
    return '(arr %s %s %s)' % (agda_ty(A[1]), agda_tm(A[2]), agda_tm(A[3]))

def agda_sub(s):
    return '⟪ ' + ' ∷ '.join(agda_tm(u) for u in s) + (' ∷ [] ⟫' if s else '[] ⟫')

_ctx_names = {}
def ctx_name(P):
    if P not in _ctx_names:
        _ctx_names[P] = 'P%d' % len(_ctx_names)
    return _ctx_names[P]

def agda_ctx(G):
    s = 'ε'
    for A in G:
        s += ' ▸ ' + agda_ty(A)
    return s
