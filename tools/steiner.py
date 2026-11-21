"""
Strict layer for the relative-coherence descent (notes/rc-generator.md §4,
step 1): the Steiner complex of a CaTT context and the cells of nu(K).

Chains are dicts basis-var -> nonnegative int, stored as sorted tuples.
A strict n-cell is a tableau: a tuple of n+1 pairs (minus_k, plus_k),
k = 0..n, with minus_n == plus_n (Steiner's nu(K)).

Everything here is strict combinatorics; no CaTT term is produced.
"""
import os, sys
from functools import lru_cache
from itertools import product
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from catt import STAR, tdim, infer, v

# ---------------------------------------------------------------- chains

def ch(d):
    return tuple(sorted((x, m) for x, m in d.items() if m))

def ch_add(a, b, k=1):
    r = dict(a)
    for x, m in b:
        r[x] = r.get(x, 0) + k * m
    return ch(r)

def ch_nonneg(a):
    return all(m >= 0 for _, m in a)

ZERO = ()

# ---------------------------------------------------------------- the complex

class Complex:
    """Steiner complex of a context G: basis = variables, deg = dimension,
    boundary signed parts d^- x, d^+ x = top chains of the strict images of
    the declared source and target."""
    def __init__(self, G):
        import rc_oracle as R
        self.G = G
        self.deg = [tdim(A) + 1 for A in G]
        self.dm, self.dp = [], []
        for x, A in enumerate(G):
            if A == STAR:
                self.dm.append(ZERO); self.dp.append(ZERO)
            else:
                self.dm.append(R._top_cached(G, A[2]))
                self.dp.append(R._top_cached(G, A[3]))
        self.n = max(self.deg) if G else 0

    def d(self, c):
        """Boundary of a chain."""
        r = ZERO
        for x, m in c:
            r = ch_add(r, self.dp[x], m)
            r = ch_add(r, self.dm[x], -m)
        return r

    def dsign(self, c, sign):
        """d^- or d^+ of a chain: positive and negative parts of d c."""
        b = self.d(c)
        if sign == '+':
            return ch({x: m for x, m in b if m > 0})
        return ch({x: -m for x, m in b if m < 0})

    def atom(self, x):
        """The tableau <x> of a basis element."""
        n = self.deg[x]
        rows = [None] * (n + 1)
        top = ((x, 1),)
        rows[n] = (top, top)
        mi = pl = top
        for k in range(n - 1, -1, -1):
            mi, pl = self.dsign(mi, '-'), self.dsign(pl, '+')
            rows[k] = (mi, pl)
        return tuple(rows)

    # -------------------------------------------------- strong Steiner test

    def strong_order(self):
        """Edges of the strong order: x < y if x in d^- y or y in d^+ x."""
        E = set()
        for y in range(len(self.G)):
            for x, _ in self.dm[y]:
                E.add((x, y))
            for z, _ in self.dp[y]:
                E.add((y, z))
        return E

    def is_loop_free_strong(self):
        E = self.strong_order()
        succ = {i: [] for i in range(len(self.G))}
        for a, b in E:
            succ[a].append(b)
        state = {}
        def dfs(a):
            state[a] = 1
            for b in succ[a]:
                if state.get(b) == 1:
                    return False
                if b not in state and not dfs(b):
                    return False
            state[a] = 2
            return True
        return all(dfs(a) for a in range(len(self.G)) if a not in state)

    def is_unital(self):
        for x in range(len(self.G)):
            a = self.atom(x)
            for c in a[0]:
                if sum(m for _, m in c) != 1:
                    return False
        return True

    def is_strong_steiner(self):
        return self.is_unital() and self.is_loop_free_strong()

# ---------------------------------------------------------------- cells of nu(K)

def cdim(c):
    return len(c) - 1

def top(c):
    return c[-1][0]

def face(c, sign):
    """The (n-1)-cell boundary of an n-cell."""
    n = cdim(c)
    rows = list(c[:n - 1])
    r = c[n - 1][0] if sign == '-' else c[n - 1][1]
    rows.append((r, r))
    return tuple(rows)

def kface(c, k, sign):
    while cdim(c) > k:
        c = face(c, sign)
    return c

def ident(c):
    n = cdim(c)
    t = top(c)
    return tuple(list(c[:n]) + [(t, t), (ZERO, ZERO)])

def raise_to(c, n):
    while cdim(c) < n:
        c = ident(c)
    return c

def comp(k, a, b):
    """a *_k b (both raised to a common dimension), or None if not composable."""
    n = max(cdim(a), cdim(b))
    a, b = raise_to(a, n), raise_to(b, n)
    if a[k][1] != b[k][0]:
        return None
    rows = []
    for j in range(n + 1):
        if j < k:
            rows.append(a[j])
        elif j == k:
            rows.append((a[k][0], b[k][1]))
        else:
            rows.append((ch_add(a[j][0], b[j][0]), ch_add(a[j][1], b[j][1])))
    return tuple(rows)

def intrinsic_rank(c):
    """h: the least rank such that c is an iterated identity on an h-cell."""
    h = cdim(c)
    while h > 0 and top(c) == ZERO and c[h - 1][0] == c[h - 1][1]:
        c = face(c, '-')
        h -= 1
    return h

def base_cell(c):
    while cdim(c) > intrinsic_rank(c):
        c = face(c, '-')
    return c

def support(K, c):
    """Closed support: basis elements in some row, closed under faces."""
    S = set()
    for mi, pl in c:
        S.update(x for x, _ in mi)
        S.update(x for x, _ in pl)
    todo = list(S)
    while todo:
        x = todo.pop()
        for row in K.atom(x):
            for chn in row:
                for y, _ in chn:
                    if y not in S:
                        S.add(y); todo.append(y)
    return S

def image_to_cell(img):
    """rc_oracle.strict_image -> tableau."""
    if img[0] == 'pt':
        t = ((img[1], 1),)
        return ((t, t),)
    n, tp, s, t = img
    cs, ct = image_to_cell(s), image_to_cell(t)
    rows = list(cs[:n - 1]) + [(cs[n - 1][0], ct[n - 1][0]), (tp, tp)]
    return tuple(rows)

# ---------------------------------------------------------------- all cells of a closed support

def cells_upto(K, S, h):
    """All cells of nu(K|S) of dimension <= h, as tableaux raised to their own
    dimension, by closure of atoms and identities under composition. Finite
    for loop-free unital K (chains are 0/1)."""
    cells = set()
    for x in S:
        if K.deg[x] <= h:
            a = K.atom(x)
            cells.add(a)
    frontier = set(cells)
    # identities
    changed = True
    while changed:
        changed = False
        new = set()
        for c in cells:
            if cdim(c) < h:
                i = ident(c)
                if i not in cells:
                    new.add(i)
        for a in cells:
            for b in cells:
                for k in range(min(cdim(a), cdim(b))):
                    r = comp(k, a, b)
                    if r is not None and r not in cells and all(ch_nonneg(m) and ch_nonneg(p) for m, p in r) \
                            and max(m for row in r for chn in row for _, m in chn) <= 1:
                        new.add(r)
        if new:
            cells |= new
            changed = True
    return cells

# ---------------------------------------------------------------- strict words (r9 Response 2; Steiner's cut formula)

def rows_above(c, r):
    """Rows of degree > r (zero rows above the dimension are dropped)."""
    return tuple(row for row in c[r + 1:] if True)

def atom_rows_eq_above(K, c, b, r):
    a = K.atom(b)
    n = max(cdim(c), cdim(a))
    ca, cb = raise_to(c, n), raise_to(a, n)
    return ca[r + 1:] == cb[r + 1:]

def zero_above(c, r):
    """c == 0 above r: c is an identity tower on an r-cell or lower."""
    return intrinsic_rank(c) <= r

def decomposition_index(K, c, S):
    """delta(c) = min r >= -1 with c ==_{r+1} 0 or c ==_{r+1} A_b."""
    for r in range(-1, cdim(c) + 1):
        if zero_above(c, r + 1):
            return r
        for b in S:
            if K.deg[b] > r + 1 and atom_rows_eq_above(K, c, b, r + 1):
                return r
    raise AssertionError('no decomposition index')

def atoms_above(K, c, r):
    """The atom multiset {A_b : |b| > r} with c ==_r sum A_b (section 1.1)."""
    n = cdim(c)
    rest = {j: (dict(c[j][0]), dict(c[j][1])) for j in range(r + 1, n + 1)}
    out = []
    for d in range(n, r, -1):
        row = rest[d][0]
        for b, m in sorted(row.items()):
            if m <= 0:
                continue
            assert K.deg[b] == d
            out += [b] * m
            a = K.atom(b)
            for j in range(r + 1, d + 1):
                for s in (0, 1):
                    for y, k in a[j][s]:
                        rest[j][s][y] = rest[j][s].get(y, 0) - m * k
    for j in rest:
        assert all(v_ == 0 for v_ in rest[j][0].values()) and all(v_ == 0 for v_ in rest[j][1].values()), \
            'rows above r are not a sum of atoms'
    return out

def cut_factors(K, c, r):
    """Steiner's cut formula: c = x_1 #_r ... #_r x_m with x_i ==_r A_i,
    the atoms sorted by a linear extension (ties by variable index)."""
    atoms = atoms_above(K, c, r)
    rowr = {b: (K.atom(b)[r][0], K.atom(b)[r][1]) for b in set(atoms)}
    def meets(a, b):
        return bool(set(x for x, _ in a) & set(x for x, _ in b))
    # order: i before j if A_i^+ meets A_j^-
    idx = list(range(len(atoms)))
    before = {i: set() for i in idx}
    for i in idx:
        for j in idx:
            if i != j and meets(rowr[atoms[i]][1], rowr[atoms[j]][0]):
                before[j].add(i)
    order, placed = [], set()
    while len(order) < len(idx):
        ready = [i for i in idx if i not in placed and before[i] <= placed]
        assert ready, 'cyclic atom order (context not loop-free?)'
        i = min(ready, key=lambda i: (atoms[i], i))
        order.append(i); placed.add(i)
    seq = [atoms[i] for i in order]
    n = cdim(c)
    h = c[r][0]
    factors = []
    for b in seq:
        a = raise_to(K.atom(b), n)
        h2 = ch_add(ch_add(h, a[r][1]), a[r][0], -1)
        rows = list(c[:r]) + [(h, h2)] + [a[j] for j in range(r + 1, n + 1)]
        factors.append(tuple(rows))
        h = h2
    assert h == c[r][1]
    return seq, factors

def strict_word(K, c, S=None):
    """An expression for the strict cell c: ('atom', b) | ('id', w) |
    ('comp', r, w1, w2), right-nested at each cut. Choices are made on the
    closed support with the given variable order."""
    if S is None:
        S = support(K, c)
    if cdim(c) > intrinsic_rank(c):
        return ('id', strict_word(K, face(c, '-'), S))
    r = decomposition_index(K, c, S)
    if r == -1:
        for b in sorted(S):
            if K.atom(b) == c:
                return ('atom', b)
        raise AssertionError('index -1 but not an atom')
    seq, factors = cut_factors(K, c, r)
    words = [strict_word(K, x, S) for x in factors]
    w = words[-1]
    for x in reversed(words[:-1]):
        w = ('comp', r, x, w)
    return w

def eval_word(K, w):
    if w[0] == 'atom':
        return K.atom(w[1])
    if w[0] == 'id':
        return ident(eval_word(K, w[1]))
    return comp(w[1], eval_word(K, w[2]), eval_word(K, w[3]))
