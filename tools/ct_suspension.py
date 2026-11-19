"""
CT for I ⊗ Dⁿ by the suspension construction of
notes/conjectures/answered/canonical-gray-terms-2026-11-19.md (§§1–4).

Builds, for n = 0..N, the family context Fam(I ⊗ Dⁿ) and a term T(c) for
every cell c of I ⊗ Dⁿ of dimension ≤ n + 1 + EXTRA (identity towers
included), by literally following the construction:

  level 0:   I = I ⊗ D⁰, context  x0 : *, x1 : *, e : x0 → x1.
  level k:   context Γ' = A, B, C, D, the two copies of Σ D^{k-1} = D^k,
             u_s : A → C, u_t : B → D, then one variable per mixed variable
             of the previous level, typed by (8); the substitution
             σ : Γ' → Σ_{A,D} Γ_{k-1} of (7)/(9); T'(Φ c̄) = (Σ T(c̄))[σ] (10).

Cells are kept abstractly together with their strict boundaries, so the
check below is exactly CT (c):  T(c) : T(∂⁻c) → T(∂⁺c) syntactically,
and CT (a): T(g) is the variable of g.  (b) holds by construction (Φ is the
strict isomorphism (5), checked in the verification note); it is not
re-checked here.

  python3 ct_suspension.py          # Python kernel check for n ≤ 4
  python3 ct_suspension.py emit     # also write src/CaTTExp/Generated/GrayIntervalDisc.agda
  python3 ct_suspension.py neg      # write a negative control (must be rejected)
"""
import sys
from catt import *
from emit_agda import Emitter

NMAX = 4
EXTRA = 1   # identity towers go one dimension above the top cell

# ------------------------------------------------------------------ suspension

def susp_ty(A):
    if A == STAR:
        return arr(STAR, v(0), v(1))
    return arr(susp_ty(A[1]), susp_tm(A[2]), susp_tm(A[3]))

def susp_tm(t):
    if t[0] == 'v':
        return v(t[1] + 2)
    _, Q, A, s = t
    return ('coh', susp_ctx(Q), susp_ty(A), (v(0), v(1)) + tuple(susp_tm(u) for u in s))

def susp_ctx(G):
    return (STAR, STAR) + tuple(susp_ty(A) for A in G)

# ------------------------------------------------------------------ whiskerings R_r, L_r of (1)

def disc_gen_vars(Q, r, first):
    """In Q = D^r ∨₀ D¹ (first=True) or D¹ ∨₀ D^r: indices of the top var of the
    disc, of its (r-1)-source and -target, and of the 1-cell h."""
    mx = maximal_vars(Q)
    a, h = (mx[0], mx[1]) if first else (mx[1], mx[0])
    return a, h

_R, _L = {}, {}
def Rterm(r):
    """R_r as a term over its own pasting context Q_r = D^r ∨₀ D¹."""
    if r in _R: return _R[r]
    Q = tree_ctx(glue_tree(r, 0, 1))
    a, h = disc_gen_vars(Q, r, True)
    if r == 1:
        tgt_h = Q[h][3]
        t = ('coh', Q, arr(STAR, Q[a][2], tgt_h), tuple(v(i) for i in range(len(Q))))
    else:
        Qm, Rm = Rterm(r - 1)
        am, hm = disc_gen_vars(Qm, r - 1, True)
        s_ = subst_tm(Rm, sub_from(Qm, Q, {am: Q[a][2], hm: v(h)}))
        t_ = subst_tm(Rm, sub_from(Qm, Q, {am: Q[a][3], hm: v(h)}))
        t = ('coh', Q, arr(infer(Q, s_), s_, t_), tuple(v(i) for i in range(len(Q))))
    infer(Q, t)
    _R[r] = (Q, t)
    return _R[r]

def Lterm(r):
    if r in _L: return _L[r]
    Q = tree_ctx(glue_tree(1, 0, r))
    a, h = disc_gen_vars(Q, r, False)
    if r == 1:
        t = ('coh', Q, arr(STAR, Q[h][2], Q[a][3]), tuple(v(i) for i in range(len(Q))))
    else:
        Qm, Lm = Lterm(r - 1)
        am, hm = disc_gen_vars(Qm, r - 1, False)
        s_ = subst_tm(Lm, sub_from(Qm, Q, {am: Q[a][2], hm: v(h)}))
        t_ = subst_tm(Lm, sub_from(Qm, Q, {am: Q[a][3], hm: v(h)}))
        t = ('coh', Q, arr(infer(Q, s_), s_, t_), tuple(v(i) for i in range(len(Q))))
    infer(Q, t)
    _L[r] = (Q, t)
    return _L[r]

def R(G, r, a_tm, h_tm):
    Q, t = Rterm(r); a, h = disc_gen_vars(Q, r, True)
    return subst_tm(t, sub_from(Q, G, {a: a_tm, h: h_tm}))

def L(G, r, h_tm, a_tm):
    Q, t = Lterm(r); a, h = disc_gen_vars(Q, r, False)
    return subst_tm(t, sub_from(Q, G, {a: a_tm, h: h_tm}))

# ------------------------------------------------------------------ identities

def ident(G, t):
    d = tdim_tm(G, t)
    Dd = tree_ctx(disc_tree(d))
    top = len(Dd) - 1
    return ('coh', Dd, arr(Dd[top], v(top), v(top)), sub_from(Dd, G, {top: t}))

# ------------------------------------------------------------------ disc generators
# D^m generators: ('g', d, '-'|'+') for d < m, ('g', m, '*').

def disc_gens(m):
    out = []
    for d in range(m):
        out += [('g', d, '-'), ('g', d, '+')]
    return out + [('g', m, '*')]

def disc_bd(g):
    _, d, _ = g
    return ('g', d - 1, '-'), ('g', d - 1, '+')

def susp_gen(g):
    return ('g', g[1] + 1, g[2])

# ------------------------------------------------------------------ levels

class Level:
    """I ⊗ D^k: context G, labels of variables, T on cells, boundaries."""

def level0():
    L0 = Level(); L0.k = 0
    L0.G = (STAR, STAR, arr(STAR, v(0), v(1)))
    pt = ('g', 0, '*')
    L0.end = {(0, pt): 0, (1, pt): 1}       # (copy, P-generator) -> var
    L0.mix = {pt: 2}                         # P-generator a -> var of e ⊗ a
    L0.cells_base = [('V', 0), ('V', 1), ('e',)]
    L0.var = {('V', 0): 0, ('V', 1): 1, ('e',): 2}
    return L0

def dim(Lv, c):
    if c[0] == 'id': return dim(Lv, c[1]) + 1
    if c[0] == 'V': return 0
    if c[0] in ('e', 'u'): return 1
    if c[0] == 'cp': return c[2][1]
    if c[0] == 'phi': return dim(Lv.prev, c[1]) + 1
    raise ValueError(c)

def bd(Lv, c):
    if c[0] == 'id': return c[1], c[1]
    if c[0] == 'e': return ('V', 0), ('V', 1)
    if c[0] == 'u': return (('V', 'A'), ('V', 'C')) if c[1] == 's' else (('V', 'B'), ('V', 'D'))
    if c[0] == 'cp':
        eps, g = c[1], c[2]
        s, t = disc_bd(g)
        def emb(h):
            if h[1] == 0:
                return ('V', {(0, '-'): 'A', (0, '+'): 'B', (1, '-'): 'C', (1, '+'): 'D'}[(eps, h[2])])
            return ('cp', eps, h)
        return emb(s), emb(t)
    if c[0] == 'phi':
        cb = c[1]
        if dim(Lv.prev, cb) == 0:
            return ('V', 'A'), ('V', 'D')
        s, t = bd(Lv.prev, cb)
        return ('phi', s), ('phi', t)
    raise ValueError(c)

def T(Lv, c):
    key = c
    if key in Lv.Tcache: return Lv.Tcache[key]
    if c[0] == 'id':
        r = ident(Lv.G, T(Lv, c[1]))
    elif c in Lv.var:
        r = v(Lv.var[c])
    elif c[0] == 'phi':
        r = subst_tm(susp_tm(T(Lv.prev, c[1])), Lv.sigma)
    else:
        raise ValueError(c)
    Lv.Tcache[key] = r
    return r

def next_level(P):
    k = P.k + 1
    Lv = Level(); Lv.k = k; Lv.prev = P; Lv.Tcache = {}
    G = [STAR] * 4                                   # A B C D
    var = {('V', X): i for i, X in enumerate('ABCD')}
    gens = [g for g in disc_gens(k) if g[1] > 0]
    vert = {(0, '-'): 0, (0, '+'): 1, (1, '-'): 2, (1, '+'): 3}
    end = {}
    for eps in (0, 1):
        for g in disc_gens(k):
            if g[1] == 0:
                end[(eps, g)] = vert[(eps, g[2])]
        for g in gens:
            s, t = disc_bd(g)
            ty = STAR if g[1] == 1 else G[end[(eps, s)]]
            G.append(arr(ty, v(end[(eps, s)]), v(end[(eps, t)])))
            end[(eps, g)] = len(G) - 1
            var[('cp', eps, g)] = len(G) - 1
    G.append(arr(STAR, v(0), v(2))); us = len(G) - 1; var[('u', 's')] = us
    G.append(arr(STAR, v(1), v(3))); ut = len(G) - 1; var[('u', 't')] = ut
    mix = {('g', 0, '-'): us, ('g', 0, '+'): ut}
    # σ : Γ' → Σ_{A,D} Γ_{k-1}, built incrementally (indices of the suspended context)
    sig = {0: v(0), 1: v(3)}
    inv_end = {i: key for key, i in P.end.items()}
    inv_mix = {i: a for a, i in P.mix.items()}
    for i, A in enumerate(P.G):
        j = i + 2
        if i in inv_end:
            eps, a = inv_end[i]
            r = a[1] + 1
            sa = susp_gen(a)
            if eps == 0:
                sig[j] = R(tuple(G), r, v(end[(0, sa)]), v(ut))
            else:
                sig[j] = L(tuple(G), r, v(us), v(end[(1, sa)]))
            # (7) must be literally well typed: the suspended declaration, substituted
            want = subst_ty(susp_ty(A), tuple(sig[x] for x in range(j)))
            assert infer(tuple(G), sig[j]) == want, ('(7) ill-typed', k, i)
        else:
            a = inv_mix[i]
            decl = subst_ty(susp_ty(A), tuple(sig[x] for x in range(j)))   # (8)
            G.append(decl)
            sig[j] = v(len(G) - 1)                                          # (9)
            mix[susp_gen(a)] = len(G) - 1
            var[('phi', ('e',) if P.k == 0 else ('mixgen', a))] = len(G) - 1
    Lv.G = tuple(G)
    Lv.sigma = tuple(sig[x] for x in range(len(P.G) + 2))
    Lv.end, Lv.mix = end, mix
    Lv.var = var
    return Lv

# The mixed generators of a level are 'e' (level 0), 'u' (the new interval
# variables) and Φ of earlier mixed generators.  Name them uniformly so that
# Φ(mixed generator) is recognised as a variable (CT (a)).
def mixed_cells(Lv):
    if Lv.k == 0:
        return {('g', 0, '*'): ('e',)}
    prev = mixed_cells(Lv.prev)
    out = {('g', 0, '-'): ('u', 's'), ('g', 0, '+'): ('u', 't')}
    for a, c in prev.items():
        out[susp_gen(a)] = ('phi', c)
    return out

def fix_vars(Lv):
    """Replace the provisional ('phi', ('mixgen', a)) keys by ('phi', cell)."""
    if Lv.k == 0: return
    fix_vars(Lv.prev)
    mc = mixed_cells(Lv.prev)
    newvar = {}
    for c, i in Lv.var.items():
        if c[0] == 'phi' and c[1][0] == 'mixgen':
            newvar[('phi', mc[c[1][1]])] = i
        else:
            newvar[c] = i
    Lv.var = newvar

# ------------------------------------------------------------------ cells

def cells(Lv, top):
    """All cells of dimension ≤ top (identity towers included), normalised:
    identities of Φ-cells are Φ of identities."""
    if Lv.k == 0:
        base = [('V', 0), ('V', 1), ('e',)]
    else:
        base = [('V', X) for X in 'ABCD']
        base += [('cp', eps, g) for eps in (0, 1) for g in disc_gens(Lv.k) if g[1] > 0]
        base += [('u', 's'), ('u', 't')]
    out = []
    for c in base:
        d = dim(Lv, c)
        while d <= top:
            out.append(c); c = ('id', c); d += 1
    if Lv.k > 0:
        out += [('phi', cb) for cb in cells(Lv.prev, top - 1)]
    return out

def build(nmax=NMAX):
    levels = [level0()]
    levels[0].Tcache = {}
    for k in range(1, nmax + 1):
        levels.append(next_level(levels[-1]))
        fix_vars(levels[-1])
    return levels

def generators(Lv):
    return list(Lv.var.keys())

def check_level(Lv, em=None, tag=''):
    check_ctx(Lv.G)
    top = Lv.k + 1 + EXTRA
    cs = cells(Lv, top)
    n = 0
    for c in cs:
        if dim(Lv, c) == 0:
            continue
        s, t = bd(Lv, c)
        Ts, Tt = T(Lv, s), T(Lv, t)
        A = STAR if dim(Lv, c) == 1 else infer(Lv.G, Ts)
        expected = arr(A, Ts, Tt)
        got = infer(Lv.G, T(Lv, c))
        assert got == expected, ('CT (c) fails', Lv.k, c)
        if em is not None:
            em.check_type('n%d-c%d%s' % (Lv.k, n, tag), Lv.G, T(Lv, c), expected)
        n += 1
    # CT (a): generators are their variables
    for c, i in Lv.var.items():
        assert T(Lv, c) == v(i), ('CT (a) fails', Lv.k, c)
    # every variable is the T of some generator
    assert sorted(Lv.var.values()) == list(range(len(Lv.G))), ('context has extra vars', Lv.k)
    return len(Lv.G), n

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'check'
    levels = build()
    em = Emitter() if mode in ('emit', 'neg') else None
    for Lv in levels:
        if Lv.k == 0:
            continue
        nv, nc = check_level(Lv, em)
        print('I ⊗ D^%d: %d variables, %d cells checked (dim ≤ %d)' % (Lv.k, nv, nc, Lv.k + 1 + EXTRA))
    if mode == 'emit':
        open('../src/CaTTExp/Generated/GrayIntervalDisc.agda', 'w').write(
            em.module('CaTTExp.Generated.GrayIntervalDisc',
                      'CT for I ⊗ Dⁿ, n ≤ %d, by the suspension construction (tools/ct_suspension.py).' % NMAX))
        print('emitted')
    if mode == 'neg':
        # Negative control: claim the top mixed generator of I ⊗ D² has its boundary swapped.
        Lv = levels[2]
        top = ('phi', ('phi', ('e',)))
        s, t = bd(Lv, top)
        A = infer(Lv.G, T(Lv, s))
        em2 = Emitter()
        em2.check_type('neg', Lv.G, T(Lv, top), arr(A, T(Lv, t), T(Lv, s)))
        open('../src/CaTTExp/Generated/NegGrayIntervalDisc.agda', 'w').write(
            em2.module('CaTTExp.Generated.NegGrayIntervalDisc', 'Negative control: must be rejected.'))
        print('negative control written')
