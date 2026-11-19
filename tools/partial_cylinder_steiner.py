"""Check (2026-11-19, relative-coherence r1 response, Followup 3 §1): for every globular
pasting diagram Q (Batanin trees up to a size bound) and every up-closed Y ⊆ Var(Q),
the complex K_Y (copies x^-, x^+ and cylinder Ix for x in Y, one copy of c not in Y,
∂Ix = x^+ − x^- − I(∂x), with c^± = c and Ic = 0) is
  - a chain complex (∂∂ = 0),
  - strongly loop-free (a <_N b if a ∈ (∂b)^- or b ∈ (∂a)^+, transitive closure acyclic),
  - unital (ε⟨b⟩_0^- = ε⟨b⟩_0^+ = 1 for every basis element),
and the atoms of the Ix satisfy the researcher's formulas (3)–(5).
Usage: python3 tools/partial_cylinder_steiner.py [max_edges]"""
import sys, itertools
from collections import defaultdict

def trees(n):
    """Batanin trees with n edges, as tuples of children."""
    if n == 0:
        yield (); return
    # first child subtree with k edges (k+1 edges incl. the edge to it), rest n-k-1
    for k in range(n):
        for c in trees(k):
            for rest in trees(n - k - 1):
                yield (c,) + rest

def globular(tree):
    """Return variables: list of (name, dim, src, tgt). Standard: tree = Σ children wedge."""
    V = []
    def build(t, prefix, d, lo, hi):
        # objects of this level: o_0..o_r ; children i between o_{i} and o_{i+1}
        # lo, hi: the (d-1)-cells bounding this hom (None at d=0)
        r = len(t)
        objs = []
        for i in range(r + 1):
            nm = prefix + ('o', i)
            V.append((nm, d, lo, hi)); objs.append(nm)
        for i, c in enumerate(t):
            build(c, prefix + ('c', i), d + 1, objs[i], objs[i + 1])
    build(tree, (), 0, None, None)
    return V

def add(a, b, s=1):
    r = dict(a)
    for k, v in b.items():
        r[k] = r.get(k, 0) + s * v
        if r[k] == 0: del r[k]
    return r

def check(tree):
    V = globular(tree)
    dim = {v[0]: v[1] for v in V}
    src = {v[0]: v[2] for v in V}; tgt = {v[0]: v[3] for v in V}
    names = [v[0] for v in V]
    cof = defaultdict(set)  # x -> cells having x as a face (immediate)
    for v in names:
        if dim[v] > 0:
            cof[src[v]].add(v); cof[tgt[v]].add(v)
    def upclosed(Y):
        return all(cof[y] <= Y for y in Y)
    results = []
    allv = names
    for k in range(len(allv) + 1):
        for Yt in itertools.combinations(allv, k):
            Y = set(Yt)
            if not upclosed(Y): continue
            # basis
            B = {}
            def cp(x, s):  # copy of x on side s
                return ('-', x) if x in Y and s == '-' else ('+', x) if x in Y else ('c', x)
            for x in allv:
                if x in Y:
                    B[('-', x)] = dim[x]; B[('+', x)] = dim[x]; B[('I', x)] = dim[x] + 1
                else:
                    B[('c', x)] = dim[x]
            def bd_glob(x, s):
                return {} if dim[x] == 0 else add({cp(tgt[x], s): 1}, {cp(src[x], s): 1}, -1)
            def I(x):
                return {('I', x): 1} if x in Y else {}
            D = {}
            for b in B:
                t, x = b
                if t in '-+c':
                    D[b] = bd_glob(x, t if t != 'c' else '+')
                else:
                    d = add({cp(x, '+'): 1}, {cp(x, '-'): 1}, -1)
                    if dim[x] > 0:
                        d = add(d, I(tgt[x]), -1); d = add(d, I(src[x]), 1)
                    D[b] = d
            def bdc(ch):
                r = {}
                for b, c in ch.items(): r = add(r, D[b], c)
                return r
            # ∂∂ = 0
            for b in B:
                assert bdc(D[b]) == {}, ('dd', tree, Y, b)
            # strong loop-freeness
            E = defaultdict(set)
            for b in B:
                for a, c in D[b].items():
                    if c < 0: E[a].add(b)
                    else: E[b].add(a)
            col = {}
            def dfs(u):
                col[u] = 1
                for w in E[u]:
                    if col.get(w) == 1: return False
                    if w not in col and not dfs(w): return False
                col[u] = 2; return True
            for b in B:
                if b not in col:
                    assert dfs(b), ('loop', tree, Y)
            # unitality and atom formulas
            def pos(ch): return {k: v for k, v in ch.items() if v > 0}
            def neg(ch): return {k: -v for k, v in ch.items() if v < 0}
            for b, n in B.items():
                lo = {b: 1}; hi = {b: 1}; seq = []
                for j in range(n):
                    lo = neg(bdc(lo)); hi = pos(bdc(hi)); seq.append((lo, hi))
                    assert all(v == 1 for v in lo.values()) and all(v == 1 for v in hi.values())
                if n > 0:
                    assert sum(lo.values()) == 1 and sum(hi.values()) == 1, ('unital', tree, Y, b)
                if b[0] == 'I':
                    x = b[1]; m = dim[x]
                    def it(f, x, j):
                        for _ in range(j): x = f[x]
                        return x
                    for j in range(1, m + 1):
                        exp_lo = add({cp(it(src, x, j - 1), '-'): 1}, I(it(tgt, x, j)))
                        exp_hi = add({cp(it(tgt, x, j - 1), '+'): 1}, I(it(src, x, j)))
                        assert seq[j - 1] == (exp_lo, exp_hi), ('atom', tree, Y, b, j, seq[j-1], exp_lo, exp_hi)
                    assert seq[m] == ({cp(it(src, x, m), '-'): 1}, {cp(it(tgt, x, m), '+'): 1}), ('atom0', tree, Y, b)
            results.append(len(Y))
    return len(results)

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    tot = 0; nt = 0
    for n in range(N + 1):
        for t in trees(n):
            tot += check(t); nt += 1
    print(f'{nt} pasting diagrams with <= {N} edges, {tot} (Q, Y) pairs: all strongly loop-free, unital, atom formulas (3)-(5) hold')
