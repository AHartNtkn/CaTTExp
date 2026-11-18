"""Strict side of RC(3) for general exchange in dimension 2
(relative-coherence.md §7.11).

For a finite 2-polygraph with an acyclic 1-graph in which every 2-generator
has nonempty source and target paths, this script checks, fibre by fibre
(every pair of parallel paths):

  T1  the exchange classes of 2-paths p => q are exactly the sets of
      linear extensions of an event poset (events = letter occurrences,
      tracked through edge instances; e < e' when e' consumes an edge
      instance that e produced, transitively), and an exchange move is
      the swap of two adjacent incomparable events;

  T2  the descent rewriting towards a fixed linear extension L0 (swap an
      adjacent pair that L0 orders the other way) terminates at L0, and
      every local branching of two descents is closed either by a square
      (disjoint swaps) or by a hexagon (three consecutive pairwise
      incomparable events).  By Squier's homotopy lemma the squares and
      hexagons generate all loops of the exchange graph.

It also counts the squares and hexagons that occur, i.e. which local
4-laws a CaTT proof has to supply, and (emit) writes an Agda module
checking the block-form hexagon and square 4-coherences.

Usage: python3 rc3_exch.py [emit|neg]
"""
import itertools
from collections import defaultdict

# ---------------------------------------------------------------- polygraphs
class Poly:
    def __init__(self, name):
        self.name = name
        self.edges = {}      # e -> (src, tgt)
        self.gens = {}       # g -> (tuple src edges, tuple tgt edges)

    def edge(self, e, a, b):
        self.edges[e] = (a, b)

    def gen(self, g, s, t):
        s, t = tuple(s), tuple(t)
        assert s and t, 'empty boundary'
        for p in (s, t):
            for e1, e2 in zip(p, p[1:]):
                assert self.edges[e1][1] == self.edges[e2][0]
        assert self.edges[s[0]][0] == self.edges[t[0]][0]
        assert self.edges[s[-1]][1] == self.edges[t[-1]][1]
        self.gens[g] = (s, t)

    def vertices(self):
        return sorted({x for ab in self.edges.values() for x in ab})

    def paths(self):
        """All nonempty paths (acyclic graph, so finitely many)."""
        out = []
        def ext(p):
            out.append(tuple(p))
            for e, (a, b) in sorted(self.edges.items()):
                if a == self.edges[p[-1]][1]:
                    ext(p + [e])
        for e in sorted(self.edges):
            ext([e])
        return out

    def steps(self, p):
        """Letters applicable to path p: (gen, position, result)."""
        for g, (s, t) in sorted(self.gens.items()):
            for i in range(len(p) - len(s) + 1):
                if p[i:i + len(s)] == s:
                    yield g, i, p[:i] + t + p[i + len(s):]

def grid(m, n):
    """Gray product of a path of length m with a path of length n.
    Squares S_ij : h_ij v_{i+1,j} => v_ij h_{i,j+1}."""
    P = Poly('grid%dx%d' % (m, n))
    for i in range(m + 1):
        for j in range(n + 1):
            if i < m: P.edge('h%d%d' % (i, j), (i, j), (i + 1, j))
            if j < n: P.edge('v%d%d' % (i, j), (i, j), (i, j + 1))
    for i in range(m):
        for j in range(n):
            P.gen('S%d%d' % (i, j), ['h%d%d' % (i, j), 'v%d%d' % (i + 1, j)],
                  ['v%d%d' % (i, j), 'h%d%d' % (i, j + 1)])
    return P

def fan(k):
    """k independent bigons side by side: x0 -> ... -> xk, a_i : e_i => e_i'."""
    P = Poly('fan%d' % k)
    for i in range(k):
        P.edge('e%d' % i, i, i + 1); P.edge("e%d'" % i, i, i + 1)
        P.gen('a%d' % i, ['e%d' % i], ["e%d'" % i])
    return P

def d2d2_skeleton():
    """2-skeleton of the cylinder of D^2 *0 D^2 (relative-coherence.md §7.9)."""
    P = Poly('D2*0D2-cyl')
    for s in '-+':
        P.edge('f0' + s, 'x' + s, 'y' + s); P.edge('f1' + s, 'x' + s, 'y' + s)
        P.edge('g0' + s, 'y' + s, 'z' + s); P.edge('g1' + s, 'y' + s, 'z' + s)
    P.edge('xu', 'x-', 'x+'); P.edge('yu', 'y-', 'y+'); P.edge('zu', 'z-', 'z+')
    P.gen('A-', ['f0-'], ['f1-']); P.gen('B-', ['g0-'], ['g1-'])
    P.gen('A+', ['f0+'], ['f1+']); P.gen('B+', ['g0+'], ['g1+'])
    for k in '01':
        P.gen('F' + k, ['f%s-' % k, 'yu'], ['xu', 'f%s+' % k])
        P.gen('G' + k, ['g%s-' % k, 'zu'], ['yu', 'g%s+' % k])
    return P

def triangle_pair():
    """Two triangles sharing nothing but a vertex, plus a bigon: mixed lengths."""
    P = Poly('triangles')
    P.edge('f', 0, 1); P.edge('g', 1, 2); P.edge('h', 0, 2)
    P.edge('k', 2, 3); P.edge('l', 3, 4); P.edge('m', 2, 4)
    P.edge('n', 4, 5); P.edge("n'", 4, 5)
    P.gen('al', ['f', 'g'], ['h']); P.gen('be', ['m'], ['k', 'l'])
    P.gen('ga', ['n'], ["n'"])
    return P

# ---------------------------------------------------------------- 2-paths
def two_paths(P, p, q, limit=200000):
    """All 2-paths p => q as tuples of (gen, pos)."""
    out = []
    def dfs(cur, w):
        if len(out) > limit: raise RuntimeError('too many 2-paths')
        if cur == q: out.append(tuple(w))
        for g, i, r in P.steps(cur):
            dfs(r, w + [(g, i)])
    dfs(p, [])
    return out

def run_word(P, p, w):
    cur = p
    for g, i in w:
        s, t = P.gens[g]
        assert cur[i:i + len(s)] == s
        cur = cur[:i] + t + cur[i + len(s):]
    return cur

def exchanges(P, p, w):
    """Words obtained from w by one exchange move (adjacent letters acting on
    disjoint segments of the intermediate path)."""
    for k in range(len(w) - 1):
        (g1, i1), (g2, i2) = w[k], w[k + 1]
        s1, t1 = P.gens[g1]; s2, t2 = P.gens[g2]
        if i2 >= i1 + len(t1):          # g2 to the right of g1's output
            nw = w[:k] + ((g2, i2 - len(t1) + len(s1)), (g1, i1)) + w[k + 2:]
        elif i2 + len(s2) <= i1:        # g2 to the left
            nw = w[:k] + ((g2, i2), (g1, i1 + len(t2) - len(s2))) + w[k + 2:]
        else:
            continue
        yield k, nw

def classes(P, p, words):
    ws = set(words); seen = set(); out = []
    for w in sorted(ws):
        if w in seen: continue
        comp = {w}; st = [w]
        while st:
            y = st.pop()
            for _, z in exchanges(P, p, y):
                assert z in ws
                if z not in comp: comp.add(z); st.append(z)
        seen |= comp; out.append(comp)
    return out

# ---------------------------------------------------------------- events
def events(P, p, w):
    """Event structure of a word: for each letter, the instances it consumes
    and produces; returns (cons, prod) lists and the direct-dependency set."""
    inst = list(range(len(p))); nxt = len(p)
    cons, prod = [], []
    for g, i in w:
        s, t = P.gens[g]
        c = inst[i:i + len(s)]
        pr = list(range(nxt, nxt + len(t))); nxt += len(t)
        inst = inst[:i] + pr + inst[i + len(s):]
        cons.append(tuple(c)); prod.append(tuple(pr))
    producer = {x: j for j, pr in enumerate(prod) for x in pr}
    less = set()
    for k, c in enumerate(cons):
        for x in c:
            if x in producer: less.add((producer[x], k))
    # transitive closure
    n = len(w); lt = [[False] * n for _ in range(n)]
    for a, b in less: lt[a][b] = True
    for m in range(n):
        for a in range(n):
            if lt[a][m]:
                for b in range(n):
                    if lt[m][b]: lt[a][b] = True
    return cons, prod, lt

def word_of_order(P, p, w, order):
    """Re-apply the events of w in the given order; None if not valid."""
    cons, prod, _ = events(P, p, w)
    inst = list(range(len(p))); out = []
    for k in order:
        c = list(cons[k]); g = w[k][0]
        for i in range(len(inst) - len(c) + 1):
            if inst[i:i + len(c)] == c:
                inst = inst[:i] + list(prod[k]) + inst[i + len(c):]
                out.append((g, i)); break
        else:
            return None
    return tuple(out)

def linear_extensions(lt):
    n = len(lt)
    def rec(done, rest):
        if not rest: yield tuple(done); return
        for k in sorted(rest):
            if all(not lt[j][k] for j in rest if j != k):
                yield from rec(done + [k], rest - {k})
    yield from rec([], frozenset(range(n)))

# ---------------------------------------------------------------- T1, T2
def check_fibre(P, p, q, stats):
    words = two_paths(P, p, q)
    for comp in classes(P, p, words):
        w0 = min(comp)
        cons, prod, lt = events(P, p, w0)
        n = len(w0)
        # T1: class = linear extensions of the event poset of w0
        lin = {}
        for order in linear_extensions(lt):
            wd = word_of_order(P, p, w0, order)
            assert wd is not None, 'linear extension not realisable'
            lin[wd] = order
        assert set(lin) == comp, ('T1 fails', P.name, p, q, w0)
        # an exchange swaps adjacent incomparable events, and conversely
        for wd, order in lin.items():
            nbrs = {z for _, z in exchanges(P, p, wd)}
            want = set()
            for k in range(n - 1):
                a, b = order[k], order[k + 1]
                if not lt[a][b]:
                    o2 = order[:k] + (b, a) + order[k + 2:]
                    want.add(word_of_order(P, p, w0, o2))
            assert nbrs == want, ('exchange != incomparable swap', P.name, wd)
        # T2: descents towards L0 = the order of w0 (identity order)
        rank = {e: k for k, e in enumerate(range(n))}
        for wd, order in lin.items():
            desc = [k for k in range(n - 1) if rank[order[k]] > rank[order[k + 1]]]
            if order != tuple(range(n)):
                assert desc, 'descent rewriting stuck before L0'
            for k in desc:
                assert not lt[order[k + 1]][order[k]] and not lt[order[k]][order[k + 1]]
            for k1, k2 in itertools.combinations(desc, 2):
                if k2 > k1 + 1:
                    stats['square'] += 1
                else:
                    a, b, c = order[k1], order[k1 + 1], order[k1 + 2]
                    assert not any(lt[x][y] for x in (a, b, c) for y in (a, b, c)), 'hexagon not antichain'
                    for perm in [(b, a, c), (b, c, a), (c, b, a), (a, c, b), (c, a, b)]:
                        assert word_of_order(P, p, w0, order[:k1] + perm + order[k1 + 3:]) is not None
                    stats['hexagon'] += 1
        stats['classes'] += 1
        stats['words'] += len(comp)
        stats['max'] = max(stats['max'], len(comp))
        stats['events'] = max(stats['events'], n)
        # pairwise-independent triples, i.e. contexts that need the hexagon law
        if any(all(not lt[x][y] for x in t3 for y in t3)
               for t3 in itertools.combinations(range(n), 3)):
            stats['cells_with_triple'] += 1

def check(P):
    stats = defaultdict(int)
    ps = P.paths()
    byend = defaultdict(list)
    for p in ps:
        byend[(P.edges[p[0]][0], P.edges[p[-1]][1])].append(p)
    for (a, b), L in byend.items():
        for p in L:
            for q in L:
                check_fibre(P, p, q, stats)
    return dict(stats)

CONTEXTS = [grid(1, 1), grid(2, 2), grid(2, 3), grid(3, 3), fan(3), fan(4),
            d2d2_skeleton(), triangle_pair()]

# ---------------------------------------------------------------- CaTT: block-form laws
def block_laws():
    """Over the pasting context D^2 v0 D^2 v0 D^2 (letters a, b, c): the six
    words, the elementary exchanges, the two hexagon routes and the hexagon
    4-coherence; over D^2 v0 D^2 v0 D^2 v0 D^2 the square of two disjoint
    exchanges.  All are single coherences over pasting contexts."""
    from catt import tree_ctx, tdim, v, infer, comp2, arr
    from rc3_grid import full_coh, id2, rnest
    from rc2 import lfold
    out = {}
    for k in (3, 4):
        P = tree_ctx(tuple(((),) for _ in range(k)))
        twos = [i for i, A in enumerate(P) if tdim(A) == 1]
        # each 2-variable z : f => g; the edges in order
        letters = [(P[i][2], P[i][3], v(i)) for i in twos]
        def letter(j, state):
            # whiskered letter j; state[i] in {0,1}: edge i is source (0) or target (1)
            parts = [z if i == j else id2(P, f if state[i] == 0 else g)
                     for i, (f, g, z) in enumerate(letters)]
            return rnest(P, parts)
        def word(order):
            st = [0] * k; ls = []
            for j in order:
                ls.append(letter(j, st)); st[j] = 1
            return lfold(P, 1, ls)
        ident = tuple(v(i) for i in range(len(P)))
        def X(o1, o2):
            return full_coh(P, word(o1), word(o2), ident)
        if k == 3:
            route1 = lfold(P, 2, [X((0, 1, 2), (1, 0, 2)), X((1, 0, 2), (1, 2, 0)), X((1, 2, 0), (2, 1, 0))])
            route2 = lfold(P, 2, [X((0, 1, 2), (0, 2, 1)), X((0, 2, 1), (2, 0, 1)), X((2, 0, 1), (2, 1, 0))])
            out['hexagon'] = (P, full_coh(P, route1, route2, ident))
        else:
            # letters 0,1 exchanged and letters 2,3 exchanged: the two orders
            r1 = lfold(P, 2, [X((0, 1, 2, 3), (1, 0, 2, 3)), X((1, 0, 2, 3), (1, 0, 3, 2))])
            r2 = lfold(P, 2, [X((0, 1, 2, 3), (0, 1, 3, 2)), X((0, 1, 3, 2), (1, 0, 3, 2))])
            out['square'] = (P, full_coh(P, r1, r2, ident))
    for P, t in out.values():
        infer(P, t)
    return out

def main():
    for P in CONTEXTS:
        s = check(P)
        print('%-12s classes %5d  words %6d  max class %4d  max events %2d  '
              'square branchings %6d  hexagon branchings %5d  cells with an independent triple %4d'
              % (P.name, s['classes'], s['words'], s['max'], s['events'],
                 s.get('square', 0), s.get('hexagon', 0), s.get('cells_with_triple', 0)))
    print('T1 and T2 hold in every fibre of every listed context')
    laws = block_laws()
    print('block-form laws:', ', '.join(sorted(laws)))
    return laws

def emit_module(neg=False):
    from emit_agda import Emitter
    from catt import arr
    laws = main()
    E = Emitter()
    if neg:
        P, t = laws['hexagon']
        from catt import infer
        A = infer(P, t)
        E.check_type('bad', P, t, arr(A[1], A[3], A[2]))
        open('../src/CaTTExp/Generated/NegExchange.agda', 'w').write(
            E.module('CaTTExp.Generated.NegExchange', 'Negative control: must be rejected.'))
        return
    for k, (P, t) in sorted(laws.items()):
        E.check_typed(k, P, t)
    src = E.module('CaTTExp.Generated.ExchangeLaws',
                   'Block-form square and hexagon 4-coherences for general exchange in dimension 2 (relative-coherence.md §7.11). Built by tools/rc3_exch.py.')
    open('../src/CaTTExp/Generated/ExchangeLaws.agda', 'w').write(src)
    print('emitted', len(E.defs), 'definitions,', len(E.checks), 'checks')

if __name__ == '__main__':
    import sys
    if sys.argv[1:] == ['emit']:
        emit_module()
    elif sys.argv[1:] == ['neg']:
        emit_module(neg=True)
    else:
        main()
