"""Exhaustive sanity checks for Theorem A* (notes/closed-structure.md, B.4):
the PL1 lemmas for the I-free Lambek calculus with product and EMPTY antecedents allowed (L*).
Adapted from scripts/pl1_check.py.
Formulas: atom 'X' | ('*',A,B) | ('\\',B,A)  (= B\\A) | ('/',A,B)  (= A/B).

For every balanced sequent up to a size bound it checks:
  C  every provable sequent has a connected formula-link graph;
  B  every premise of every applicable rule instance with provable premises is balanced;
  S  for each principal formula, at most one split gives provable premises
     (splits are forced);
  F  (provability shadow of Lemma F*/T*): if a left rule at H has the
     F*-hypothesis (Delta u {B} link-closed, contiguous, adjacent, goal not in it)
     and the sequent is provable, then both premises are provable;
     likewise for R(*) with the T*-hypothesis.
"""
import itertools, sys
from functools import lru_cache

def is_atom(f): return isinstance(f, str)

@lru_cache(maxsize=None)
def prov(ctx, goal):
    """ctx: tuple of formulas (nonempty)."""
    for _ in rules(ctx, goal):
        return True
    return False

def rules(ctx, goal):
    """Yield (name, principal, premises) for rule instances whose premises are all provable."""
    n = len(ctx)
    if n == 1 and is_atom(goal) and ctx[0] == goal:
        yield ('ax', None, ())
    if not is_atom(goal):
        op = goal[0]
        if op == '\\':
            B, A = goal[1], goal[2]
            if prov((B,) + ctx, A): yield ('R\\', 'goal', (((B,)+ctx, A),))
        elif op == '/':
            A, B = goal[1], goal[2]
            if prov(ctx + (B,), A): yield ('R/', 'goal', ((ctx+(B,), A),))
        else:
            C1, C2 = goal[1], goal[2]
            for k in range(0, n + 1):
                if prov(ctx[:k], C1) and prov(ctx[k:], C2):
                    yield ('R*', ('goal', k), ((ctx[:k], C1), (ctx[k:], C2)))
    for i, H in enumerate(ctx):
        if is_atom(H): continue
        op = H[0]
        if op == '*':
            c2 = ctx[:i] + (H[1], H[2]) + ctx[i+1:]
            if prov(c2, goal): yield ('L*', i, ((c2, goal),))
        elif op == '\\':
            B, A = H[1], H[2]
            for j in range(0, i + 1):   # Delta = ctx[j:i], possibly empty
                D = ctx[j:i]
                rest = ctx[:j] + (A,) + ctx[i+1:]
                if prov(D, B) and prov(rest, goal):
                    yield ('L\\', (i, j), ((D, B), (rest, goal)))
        else:
            A, B = H[1], H[2]
            for j in range(i+1, n+1):
                D = ctx[i+1:j]
                rest = ctx[:i] + (A,) + ctx[j:]
                if prov(D, B) and prov(rest, goal):
                    yield ('L/', (i, j), ((D, B), (rest, goal)))

def occ(f, pol, acc, node):
    """Collect (atom, polarity, node) occurrences; pol +1 positive."""
    if is_atom(f): acc.append((f, pol, node)); return
    op = f[0]
    if op == '*': occ(f[1], pol, acc, node); occ(f[2], pol, acc, node)
    elif op == '\\': occ(f[1], -pol, acc, node); occ(f[2], pol, acc, node)
    else: occ(f[1], pol, acc, node); occ(f[2], -pol, acc, node)

def occurrences(ctx, goal, split=None):
    """Nodes: hypotheses 0..n-1, goal 'g'. split=(i,'B'/'A' handled by caller)."""
    acc = []
    for i, H in enumerate(ctx): occ(H, -1, acc, i)
    occ(goal, +1, acc, 'g')
    return acc

def balanced(ctx, goal):
    acc = occurrences(ctx, goal)
    from collections import Counter
    c = Counter((a, p) for a, p, _ in acc)
    atoms = {a for a, _, _ in acc}
    return all(c[(a, 1)] == 1 and c[(a, -1)] == 1 for a in atoms)

def links(acc):
    by = {}
    for a, p, node in acc: by.setdefault(a, []).append(node)
    return [tuple(v) for v in by.values()]

def components(nodes, edges):
    parent = {x: x for x in nodes}
    def find(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for a, b in edges: parent[find(a)] = find(b)
    comps = {}
    for x in nodes: comps.setdefault(find(x), set()).add(x)
    return list(comps.values())

def graph(ctx, goal, splitH=None, splitgoal=False):
    """Formula-level link graph; optionally split hypothesis splitH into ('B',i),('A',i)
    or the goal into ('g1'),('g2')."""
    acc = []
    nodes = []
    for i, H in enumerate(ctx):
        if i == splitH:
            op = H[0]
            if op == '\\': occ(H[1], +1, acc, ('B', i)); occ(H[2], -1, acc, ('A', i))
            else: occ(H[1], -1, acc, ('A', i)); occ(H[2], +1, acc, ('B', i))
            nodes += [('B', i), ('A', i)]
        else:
            occ(H, -1, acc, i); nodes.append(i)
    if splitgoal:
        occ(goal[1], +1, acc, 'g1'); occ(goal[2], +1, acc, 'g2'); nodes += ['g1', 'g2']
    else:
        occ(goal, +1, acc, 'g'); nodes.append('g')
    return nodes, links(acc)

def linkclosed(S, edges):
    return all((a in S) == (b in S) for a, b in edges)

# ---------- enumeration of balanced sequents ----------
def shapes(k):
    """Formula shapes with k leaves ('_' placeholders)."""
    if k == 1: yield '_'; return
    for l in range(1, k):
        for a in shapes(l):
            for b in shapes(k - l):
                for op in ('*', '\\', '/'):
                    yield (op, a, b)

def fill(shape, it):
    if shape == '_': return next(it)
    return (shape[0], fill(shape[1], it), fill(shape[2], it))

def leaves(shape): return 1 if shape == '_' else leaves(shape[1]) + leaves(shape[2])

def sequents(total_leaves, maxctx=3):
    for m in range(0, maxctx + 1):          # number of hypotheses
        for parts in itertools.product(range(1, total_leaves + 1), repeat=m + 1):
            if sum(parts) != total_leaves: continue
            for shs in itertools.product(*[list(shapes(p)) for p in parts]):
                yield shs

def labellings(n):
    """All ways to pair n leaf positions into n/2 atoms (canonical names)."""
    if n % 2: return
    def rec(rem):
        if not rem: yield {}; return
        a = rem[0]
        for b in rem[1:]:
            r2 = [x for x in rem if x not in (a, b)]
            for m in rec(r2):
                m2 = dict(m); m2[a] = m2[b] = len(rem)
                yield m2
    yield from rec(list(range(n)))

def main(maxleaves):
    stats = dict(seq=0, provable=0, rules=0)
    for L in range(2, maxleaves + 1, 2):
        for shs in sequents(L):
            for lab in labellings(L):
                names = ['X%d' % lab[i] for i in range(L)]
                it = iter(names)
                fs = [fill(s, it) for s in shs]
                ctx, goal = tuple(fs[:-1]), fs[-1]
                if not balanced(ctx, goal): continue
                stats['seq'] += 1
                if not prov(ctx, goal): 
                    check_F(ctx, goal, provable=False); continue
                stats['provable'] += 1
                nodes, edges = graph(ctx, goal)
                assert len(components(nodes, edges)) == 1, ('C fails', ctx, goal)
                seen = {}
                for name, princ, prem in rules(ctx, goal):
                    stats['rules'] += 1
                    for (c, g) in prem: assert balanced(c, g), ('B fails', ctx, goal, name)
                    key = (name, princ if name in ('R\\','R/','L*','ax') else (princ[0] if name != 'R*' else 'goal'))
                    assert key not in seen or seen[key] == prem, ('S fails', ctx, goal, name)
                    seen[key] = prem
                check_F(ctx, goal, provable=True)
    print(stats)

def check_F(ctx, goal, provable):
    if not provable: return
    n = len(ctx)
    for i, H in enumerate(ctx):
        if is_atom(H) or H[0] == '*': continue
        nodes, edges = graph(ctx, goal, splitH=i)
        rng = range(0, i + 1) if H[0] == '\\' else range(i + 1, n + 1)
        for j in rng:
            D = list(range(j, i)) if H[0] == '\\' else list(range(i + 1, j))
            S = set(D) | {('B', i)}
            if linkclosed(S, edges):
                if H[0] == '\\':
                    B, A = H[1], H[2]; Dc = ctx[j:i]; rest = ctx[:j] + (A,) + ctx[i+1:]
                else:
                    A, B = H[1], H[2]; Dc = ctx[i+1:j]; rest = ctx[:i] + (A,) + ctx[j:]
                assert prov(Dc, B) and prov(rest, goal), ('F fails', ctx, goal, i, j)
    if not is_atom(goal) and goal[0] == '*':
        nodes, edges = graph(ctx, goal, splitgoal=True)
        for k in range(0, n + 1):
            S = set(range(k)) | {'g1'}
            if linkclosed(S, edges):
                assert prov(ctx[:k], goal[1]) and prov(ctx[k:], goal[2]), ('T fails', ctx, goal, k)

if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 6)
