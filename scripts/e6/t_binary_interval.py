"""The theory T of answered/lax-interchange-construction-or-impossibility-2026-11-19.md on Gamma = SigmaD2 v SigmaD2.

Global 2-cells alpha, alpha' (left) and beta, beta' (right); 3-cells A : alpha => alpha', B : beta => beta';
the outer crossing C = chi : (beta alpha) => (alpha beta). The 3-paths from beta alpha to alpha' beta' are the
orderings of the moves A, B, C (each once). T's 4-generators acting on adjacent moves (all other T generators
need a composite or whiskered 2-cell argument, absent here, so (15)-(16) are vacuous):
  t(alpha, B) : B C => C B           r(A, beta) : C A => A C
  iota(F, G)  : right-interval move first => left-interval move first, for two non-crossing moves.
Before C the 2-word is beta alpha (beta left), after C it is alpha beta (alpha left).
The script prints the 4-generator graph and checks which routes S = BCA -> T = ACB exist.
Run: python3 scripts/e6/t_binary_interval.py
"""
from itertools import permutations

def word_before(path, i):            # positions before move i: is C already done?
    return 'ab' if 'C' in path[:i] else 'ba'

def left_cell(word):                 # which cell is positionally left
    return 'A' if word == 'ab' else 'B'

edges = []
for p in map(''.join, permutations('ABC')):
    for i in range(2):
        x, y = p[i], p[i + 1]
        q = p[:i] + y + x + p[i + 2:]
        if (x, y) == ('B', 'C'): edges.append((p, q, 't'))
        elif (x, y) == ('C', 'A'): edges.append((p, q, 'r'))
        elif {x, y} == {'A', 'B'}:
            left = left_cell(word_before(p, i))
            if y == left:            # x (right) first => y (left) first
                edges.append((p, q, 'iota'))
names = {'BCA': 'S', 'CBA': 'V0', 'CAB': 'V1', 'ACB': 'T', 'ABC': 'U0', 'BAC': 'U1'}
for s, t, k in edges: print(f'  {names[s]:>2} -> {names[t]:<2} {k}')

def routes(s, t):
    out = []
    def go(v, acc):
        if v == t: out.append(acc); return
        for a, b, k in edges:
            if a == v: go(b, acc + [(k, names[a] + '->' + names[b])])
    go(s, []); return out
rs = routes('BCA', 'ACB')
print('4-paths S -> T:', rs)
assert len(rs) == 1, 'expected exactly one route'
assert [k for k, _ in rs[0]] == ['t', 'iota', 'r']
sinks = sorted(names[v] for v in names if not any(a == v for a, _, _ in edges))
print('sinks:', sinks)
assert 'U1' in sinks
print('Only t0 ; iota(A,B) ; r0 joins S to T: the route through r1 = (S -> U1) and t1 = (U0 -> T) does not exist,')
print('so no 5-cell can lift A (x) B over T as given; dimension-4 data must be added (cf. K8, K10).')
