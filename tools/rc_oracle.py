"""
Relative-coherence oracle: rc(G, A, t, u) -> term w with G |- w : t ->_A u, or None.

Untrusted generator. Every answer is re-checked by catt.infer here, and the
emitted Agda table (see `emit_table`) asks the certified checker
CaTTExp.Check to infer each answer's type and asserts it by refl.

Interface (mirrors the Agda signature rc : Ctx -> Ty -> Tm -> Tm -> Maybe Tm):
  rc(G, A, t, u)  with G a context, A a type, t, u terms of G of type A.
It returns None when
  - t or u does not have type A, or
  - the strict images of t and u differ (`strict_image`), or
  - the dimension is not covered yet (see `covered`).

Strict images.  For a strong Steiner context (every context the project uses
RC on: cylinders, cones, Gray products of globes) the free strict
omega-category on G is Steiner's nu(K), so a strict n-cell is determined by
its top chain (a formal sum of n-variables) together with the strict images
of its two faces. `strict_image` computes exactly that tableau. It does not
check that G is strong Steiner; on a context that is not, equality of
tableaux can be coarser than equality in the free strict category, and the
constructors below may then fail (they raise, and rc returns None). No
wrong answer can result: every output is type-checked.

Dimensions covered.
  n = 0  : equal objects are literally equal; identity.
  n = 1  : RC(1), every context (relative-coherence.md section 1): the
           coherence over the chain context of the common path.
  n = 2  : Theorem A (relative-coherence.md section 2), via tools/rc2.py,
           on the support of t, u (dimension <= 2, acyclic 1-skeleton).
  n >= 3 : globular supports and common factors as above; otherwise the
           local reductions of rc_heur.py (top-slot congruence, identity
           slots, distribution, rebracketing, abstraction to a pasting
           context). The r9 Response 15 descent is not implemented yet.

Support restriction. Every call is answered on the dependency-closed
support S of (A, t, u). The answer over G|S is pulled back along the
inclusion G|S -> G.
"""
from functools import lru_cache
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from catt import *
import rc2 as _rc2
import rc_dim2 as _rcd2

# ---------------------------------------------------------------- strict images

def tm_dim(G, t):
    return tdim(infer(G, t)) + 1

def _add(c, d, k=1):
    r = dict(c)
    for x, m in d.items():
        r[x] = r.get(x, 0) + k * m
        if r[x] == 0:
            del r[x]
    return r

def top_chain(G, t):
    """Top chain of the strict image of t, as a sorted tuple of (var, coeff)."""
    return tuple(sorted(_top(G, t).items()))

@lru_cache(maxsize=None)
def _top_cached(G, t):
    if t[0] == 'v':
        return ((t[1], 1),)
    _, P, A, s = t
    N = tdim(A) + 1
    if ps_dim(P) != N:
        return ()                      # a coherence of identity type
    c = {}
    for i, B in enumerate(P):
        if tdim(B) + 1 == N:
            c = _add(c, dict(_top_cached(G, s[i])))
    return tuple(sorted(c.items()))

def _top(G, t):
    return dict(_top_cached(G, t))

@lru_cache(maxsize=None)
def strict_image(G, t):
    """Steiner tableau of the strict image: (dim, top chain, image of source,
    image of target); objects are ('pt', x)."""
    A = infer(G, t)
    if A == STAR:
        assert t[0] == 'v'
        return ('pt', t[1])
    return (tdim(A) + 1, _top_cached(G, t), strict_image(G, A[2]), strict_image(G, A[3]))

# ---------------------------------------------------------------- support restriction

def support(G, vs):
    """Dependency closure of a set of variables."""
    S, todo = set(), list(vs)
    while todo:
        i = todo.pop()
        if i in S:
            continue
        S.add(i)
        todo.extend(fv_ty(G[i]))
    return S

def _ren_tm(t, ren):
    if t[0] == 'v':
        return v(ren[t[1]])
    return ('coh', t[1], t[2], tuple(_ren_tm(u, ren) for u in t[3]))

def _ren_ty(A, ren):
    if A == STAR:
        return A
    return ('->', _ren_ty(A[1], ren), _ren_tm(A[2], ren), _ren_tm(A[3], ren))

def restrict_to(G, A, t, u):
    S = support(G, set(fv_ty(A)) | set(fv_tm(t)) | set(fv_tm(u)))
    order = sorted(S)
    ren = {old: new for new, old in enumerate(order)}
    H = tuple(_ren_ty(G[o], ren) for o in order)
    incl = tuple(v(o) for o in order)          # substitution H -> G
    return H, incl, _ren_ty(A, ren), _ren_tm(t, ren), _ren_tm(u, ren)

# ---------------------------------------------------------------- identities

def identity(G, t):
    """The identity coherence on an n-term t: coh_{D^n : x -> x}[t]."""
    A = infer(G, t)
    n = tdim(A) + 1
    D = tree_ctx(disc_tree(n))
    top = len(D) - 1
    s = sub_from(D, G, {top: t})
    B = D[top]
    return ('coh', D, arr(B, v(top), v(top)), s)

# ---------------------------------------------------------------- RC(1)

def _vpos(p):
    """Level of the p-th vertex of the chain context tree_ctx(chain_tree(k))."""
    return 0 if p == 0 else 2 * p - 1

def _epos(p):
    return 2 * p + 2

def path1(G, a):
    """Flattened edge word of a 1-term (identities flatten to the empty word)."""
    if a[0] == 'v':
        return (a[1],)
    _, P, A, s = a
    out = ()
    for i, B in enumerate(P):
        if tdim(B) == 0:
            out += path1(G, s[i])
    return out

def pull1(G, a, off):
    """The 1-term a, whose path occupies positions [off, off+len) of a chain,
    rewritten over that chain context (positions, not vertices of G)."""
    if a[0] == 'v':
        return v(_epos(off))
    _, P, A, s = a
    # assign vertex positions: vertex 0 at off; target of edge i at the end of it
    out = [None] * len(P)
    pos = off
    for i, B in enumerate(P):
        d = tdim(B) + 1
        if i == 0:
            out[i] = v(_vpos(pos))
        elif d == 0:
            pass                        # set when its edge is processed
        else:
            out[i] = pull1(G, s[i], pos)
            pos += len(path1(G, s[i]))
            tgt_var = B[3][1]
            out[tgt_var] = v(_vpos(pos))
    if ps_dim(P) == 0:
        out = [v(_vpos(off))]
    return ('coh', P, A, tuple(out))

def kappa1(G, a, b):
    """RC(1): a -> b for parallel 1-terms with the same path."""
    A = infer(G, a)
    assert A == infer(G, b) and tdim(A) == 0
    w = path1(G, a)
    if w != path1(G, b):
        return None
    C = tree_ctx(chain_tree(len(w)))
    at, bt = pull1(G, a, 0), pull1(G, b, 0)
    iota = [None] * len(C)
    iota[0] = A[2]
    for p, e in enumerate(w):
        iota[_epos(p)] = v(e)
        iota[_vpos(p + 1)] = G[e][3]
    iota = tuple(iota)
    assert subst_tm(at, iota) == a and subst_tm(bt, iota) == b, 'pull1 mismatch'
    TA = infer(C, at)
    return ('coh', C, arr(TA, at, bt), iota)

# ---------------------------------------------------------------- the oracle

class NotCovered(Exception):
    pass

def covered(n):
    return n <= 2

def rc(G, A, t, u):
    """Return w : t ->_A u in G, or None. Never returns an ill-typed term."""
    try:
        check_ctx(G)
        if infer(G, t) != A or infer(G, u) != A:
            return None
        if strict_image(G, t) != strict_image(G, u):
            return None
        import rc_heur
        rc_heur.CALLS[0] = 0
        w = _rc(G, A, t, u)
    except (TypeError_, AssertionError, NotCovered, KeyError, StopIteration, ValueError):
        return None
    if w is None:
        return None
    assert infer(G, w) == arr(A, t, u), 'oracle produced an ill-typed answer'
    return w

def _rc_inner(G, A, t, u):
    # a sub-query that fails by an exception fails alone (other routes of
    # the caller stay open); only the call budget (NotCovered) aborts
    try:
        if infer(G, t) != A or infer(G, u) != A:
            return None
        return _rc(G, A, t, u)
    except (TypeError_, AssertionError, KeyError, StopIteration, ValueError):
        return None

def _rc(G, A, t, u):
    n = tdim(A) + 1
    if t == u:
        return identity(G, t)
    if n == 0:
        return None
    H, incl, AH, tH, uH = restrict_to(G, A, t, u)
    w = globular_comparison(H, AH, tH, uH)
    if w is None and n >= 1:
        w = peel(H, AH, tH, uH, _rc_inner)
    if w is not None:
        return subst_tm(w, incl)
    if n == 1:
        w = kappa1(H, tH, uH)
    elif n == 2:
        w = _rcd2.rc2_small(H, tH, uH)
    else:
        import rc_heur
        w = rc_heur.heur(H, AH, tH, uH, _rc_inner)
    if w is None:
        return None
    return subst_tm(w, incl)

# ---------------------------------------------------------------- Agda tables

GEN = os.path.join(os.environ.get('CATT_SRC') or os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'), 'CaTTExp', 'Generated')

def emit_table(modname, answered, comment=''):
    """answered: list of (G, A, t, u, w). Writes a module defining
    `entries : List Entry`, `rc : Oracle` and `all-certified`, the
    certified checker's verdict on every entry, proved by refl."""
    from emit_agda import Emitter
    E = Emitter()
    rows = []
    for (G, A, t, u, w) in answered:
        rows.append('entry %s %s %s %s %s' % (E.ctx(G), E.ty(A), E.tm(t), E.tm(u), E.tm(w)))
    out = ['-- Generated by tools/rc_oracle.py. Do not edit. ' + comment,
           'module CaTTExp.Generated.%s where' % modname, '',
           'open import CaTTExp.Prelude', 'open import CaTTExp.Pure',
           'open import CaTTExp.RCOracle', '',
           'v : Nat → Tm', 'v = var', '']
    out += E.defs
    out += ['entries : List Entry',
            'entries =' + ''.join('\n  %s ∷' % r for r in rows) + ' []', '',
            'rc : Oracle', 'rc = fromTable entries', '']
    return '\n'.join(out)

def emit_check(modname):
    """Separate module: the certified checker's verdict on every entry, by refl.
    Kept apart from the table so that loading the table stays cheap."""
    return '\n'.join([
        '-- Generated by tools/rc_oracle.py. Do not edit.',
        'module CaTTExp.Generated.%sCheck where' % modname, '',
        'open import CaTTExp.Prelude', 'open import CaTTExp.RCOracle',
        'open import CaTTExp.Generated.%s' % modname, '',
        '-- The certified checker accepts every answer at exactly its queried type.',
        'all-certified : certified? entries ≡ true',
        'all-certified = refl', ''])

def write_table(modname, queries, comment=''):
    answered, missing = [], []
    for (G, A, t, u) in queries:
        w = rc(G, A, t, u)
        if w is None:
            missing.append((G, A, t, u))
        else:
            answered.append((G, A, t, u, w))
    path = os.path.join(GEN, modname + '.agda')
    with open(path, 'w') as f:
        f.write(emit_table(modname, answered, comment))
    with open(os.path.join(GEN, modname + 'Check.agda'), 'w') as f:
        f.write(emit_check(modname))
    print('%s: %d answered, %d unanswered' % (path, len(answered), len(missing)))
    return answered, missing

def emit_queries(modname, queries):
    """A module exposing `queries : List Query` (used for round-trip tests)."""
    from emit_agda import Emitter
    E = Emitter()
    rows = ['query %s %s %s %s' % (E.ctx(G), E.ty(A), E.tm(t), E.tm(u)) for (G, A, t, u) in queries]
    out = ['-- Generated by tools/rc_oracle.py.', 'module %s where' % modname, '',
           'open import CaTTExp.Prelude', 'open import CaTTExp.Pure',
           'open import CaTTExp.RCOracle', '', 'v : Nat → Tm', 'v = var', '']
    out += E.defs
    out += ['queries : List Query', 'queries =' + ''.join('\n  %s ∷' % r for r in rows) + ' []', '']
    return '\n'.join(out)

# ---------------------------------------------------------------- globular supports (r9 Response 2)

def globular_order(G):
    """If G is literally globular (every declared face is a variable) and the
    relation s(x) < x < t(x) generates a strict total order, return that
    order as a list of levels; else None."""
    succ = {i: set() for i in range(len(G))}
    indeg = {i: 0 for i in range(len(G))}
    for x, A in enumerate(G):
        if A == STAR:
            continue
        s, t = A[2], A[3]
        if s[0] != 'v' or t[0] != 'v':
            return None
        for a, b in ((s[1], x), (x, t[1])):
            if b not in succ[a]:
                succ[a].add(b); indeg[b] += 1
    order, ready = [], [i for i in range(len(G)) if indeg[i] == 0]
    while ready:
        if len(ready) != 1:
            return None                 # not a total order
        a = ready.pop()
        order.append(a)
        for b in succ[a]:
            indeg[b] -= 1
            if indeg[b] == 0:
                ready.append(b)
    return order if len(order) == len(G) else None

def globular_comparison(G, A, t, u):
    """Response 2, 'comparisons on a globular support': when the context (already
    restricted to the support) is a pasting context up to renumbering, one
    coherence head t -> u, pulled back along the renumbering."""
    order = globular_order(G)
    if order is None:
        return None
    dims = {i: tdim(G[i]) + 1 for i in range(len(G))}
    def rec(seq, first):
        k = dims[seq[0]]
        out = [seq[0]] if first else []
        cuts = [j for j, x in enumerate(seq) if dims[x] == k]
        for a, b in zip(cuts, cuts[1:]):
            block = seq[a + 1:b]
            if not block or min(dims[x] for x in block) != k + 1:
                raise ValueError('not a pasting order')
            out += [seq[b], block[0]] + rec(block, False)
        return out
    try:
        order = rec(order, True)
    except (ValueError, IndexError):
        return None
    ren = {old: new for new, old in enumerate(order)}
    P = tuple(_ren_ty(G[o], ren) for o in order)
    if not is_ps(P):
        return None
    At, tt, ut = _ren_ty(A, ren), _ren_tm(t, ren), _ren_tm(u, ren)
    if not side_ok(P, At, tt, ut):
        return None
    back = tuple(v(o) for o in order)          # P -> G
    return ('coh', P, arr(At, tt, ut), back)

# ---------------------------------------------------------------- peeling common vertical factors

def column_tree(n, k):
    """Pasting tree of k n-disks composed along their (n-1)-faces."""
    if n == 1:
        return tuple(() for _ in range(k))
    return (column_tree(n - 1, k),)

def _is_column(P, n):
    t = tree_of(P)
    if t is None:
        return None
    for k in range(1, len(P)):
        if column_tree(n, k) == t:
            return k
    return None

def vfactors(G, t, n):
    """The factors of t along its top cut n-1: t is flattened through
    composition coherences over column pasting contexts."""
    if t[0] == 'coh':
        _, P, A, s = t
        if tdim(A) + 1 == n and ps_dim(P) == n and _is_column(P, n):
            out = []
            for i, B in enumerate(P):
                if tdim(B) + 1 == n:
                    out += vfactors(G, s[i], n)
            return out
    return [t]

def _abstract(G, t, n, C, tops, pos):
    """t as a term over the column context C, its factors at C's top
    variables tops[pos[0]], tops[pos[0]+1], ..."""
    if t[0] == 'coh':
        _, P, A, s = t
        if tdim(A) + 1 == n and ps_dim(P) == n and _is_column(P, n):
            im = {}
            for i, B in enumerate(P):
                if tdim(B) + 1 == n:
                    im[i] = _abstract(G, s[i], n, C, tops, pos)
            return ('coh', P, A, sub_from(P, C, im))
    x = v(tops[pos[0]])
    pos[0] += 1
    return x

def column(n, k):
    C = tree_ctx(column_tree(n, k))
    tops = [i for i, B in enumerate(C) if tdim(B) + 1 == n]
    return C, tops

def vcomp_over(C, tops, n, lo, hi):
    """Right-nested composite of the top variables tops[lo:hi] over C (an
    identity on the shared face when lo == hi)."""
    if lo == hi:
        # the (n-1)-cell between tops[lo-1] and tops[lo]
        if lo < len(tops):
            face = infer(C, v(tops[lo]))[2]
        else:
            face = infer(C, v(tops[lo - 1]))[3]
        return identity(C, face)
    w = v(tops[hi - 1])
    for j in range(hi - 2, lo - 1, -1):
        w = comp2(C, n - 1, v(tops[j]), w)
    return w

def peel(G, A, t, u, rec):
    """If t and u share a literal prefix or suffix of top-cut factors, compare
    the middles (by `rec`) and whisker; the rebracketings are single
    coherences over column contexts."""
    n = tdim(A) + 1
    ft, fu = vfactors(G, t, n), vfactors(G, u, n)
    p = 0
    while p < min(len(ft), len(fu)) and ft[p] == fu[p]:
        p += 1
    q = 0
    while q < min(len(ft), len(fu)) - p and ft[-1 - q] == fu[-1 - q]:
        q += 1
    if p == 0 and q == 0:
        return None
    mt, mu = ft[p:len(ft) - q], fu[p:len(fu) - q]
    if not mt and not mu:
        return None                    # t, u differ only in bracketing: let the caller handle it
    def side(fs, mid, term):
        k = len(fs)
        C, tops = column(n, k)
        sub = sub_from(C, G, {tops[i]: fs[i] for i in range(k)})
        T = _abstract(G, term, n, C, tops, [0])
        assert subst_tm(T, sub) == term
        # bracket: (prefix) * ((mid) * (suffix)), each part right nested
        parts = []
        if p: parts.append(vcomp_over(C, tops, n, 0, p))
        parts.append(vcomp_over(C, tops, n, p, p + len(mid)))
        if q: parts.append(vcomp_over(C, tops, n, k - q, k))
        B = parts[-1]
        for x in reversed(parts[:-1]):
            B = comp2(C, n - 1, x, B)
        TA = infer(C, T)
        to_b = None if T == B else ('coh', C, arr(TA, T, B), sub)
        from_b = None if T == B else ('coh', C, arr(TA, B, T), sub)
        return subst_tm(B, sub), subst_tm(parts[1 if p else 0], sub), to_b, from_b
    Bt, Mt, t_to, _ = side(ft, mt, t)
    Bu, Mu, _, u_from = side(fu, mu, u)
    X = rec(G, infer(G, Mt), Mt, Mu)
    if X is None:
        return None
    # whisker X by the prefix and suffix composites
    W = X
    if q:
        sfx = vcomp_over_terms(G, n, ft[len(ft) - q:])
        W = comp2(G, n - 1, W, sfx)
    if p:
        pfx = vcomp_over_terms(G, n, ft[:p])
        W = comp2(G, n - 1, pfx, W)
    assert infer(G, W)[2] == Bt and infer(G, W)[3] == Bu, 'peel: whiskered middle has wrong ends'
    cells = [c for c in (t_to, W, u_from) if c is not None]
    out = cells[0]
    for c in cells[1:]:
        out = comp2(G, n, out, c)
    return out

def vcomp_over_terms(G, n, fs):
    w = fs[-1]
    for x in reversed(fs[:-1]):
        w = comp2(G, n - 1, x, w)
    return w
