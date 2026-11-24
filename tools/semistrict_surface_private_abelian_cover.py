"""Decide private degree-four surface movies on abelian positioned history groups.

On other components a negative abelian-cover comparison still excludes a filler.
--faces FILE uses the positioned private movie format. Requires islpy.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from functools import reduce
from itertools import combinations
import json
from pathlib import Path

import islpy as isl

from semistrict_surface_history_group import HistoryGroup
from semistrict_surface_private_winding import solve as winding
from semistrict_surface_shared_edge import braid_image


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def point(values):
    return isl.Set('{ ['+','.join(map(str, values))+'] }')


def coords(prefix, k):
    return [prefix+str(i) for i in range(k)]


class Cover:
    def __init__(self, history, marks):
        h = tuple((p, e) for e, (p, _) in enumerate(history))
        ports = {e: marks[label] for e, (_, label) in enumerate(history)}
        group = HistoryGroup(h, ports)
        self.n = len(h)
        self.histories = list(group.tree_paths)
        index = {h: i for i, h in enumerate(self.histories)}
        # Quotient edge counts by the rational span of all Artin relators.
        rels = list(group.relators)
        mat = isl.Mat.alloc(isl.DEFAULT_CONTEXT, len(rels), len(group.generators))
        for i, rel in enumerate(rels):
            count = Counter(rel)
            for g in range(1, len(group.generators)+1):
                mat = mat.set_element_val(i, g-1, count[g]-count[-g])
        weights = mat.right_kernel()
        self.rank = weights.cols()
        zero = self.zero = (0,)*self.rank
        self.edges = [dict() for _ in index]
        self.reachable = {}
        for (h, i), word in group.labels.items():
            dest, _ = group.read(h, (i,))
            v = (tuple(weights.get_element_val(word[0]-1, j).to_python() for j in range(self.rank))
                 if word else zero)
            a, b = index[h], index[dest]
            self.edges[a][i] = b, v
            self.edges[b][-i] = a, neg(v)
        # Deduplicate the actual braid generators before testing commutation.
        loops = {braid_image(self.n, w): w for w in group.braids.values()}
        loops.pop(braid_image(self.n, ()), None)
        self.abelian = all(braid_image(self.n, a+b) == braid_image(self.n, b+a)
                           for a, b in combinations(loops.values(), 2))

    def read(self, steps):
        h, v, pure = 0, self.zero, []
        counts, marks = defaultdict(int), {}
        for op, i in steps:
            if op == 'X':
                pure.append(i+1)
                h, move = self.edges[h][i+1]
                v = add(v, move)
            else:
                e = self.histories[h][i][1]
                marks[e, counts[e]] = (h, *v)
                counts[e] += 1
        return marks, braid_image(self.n, pure)

    def relation(self, edges):
        x = coords('x', self.rank)
        def side(h, cells):
            return '['+','.join([str(h), *cells])+']'
        branches = []
        for h, k, shift, loops in edges:
            ys = [f'{v}+({d})' for v, d in zip(x, shift)]
            # Local circuit multiplicities may be any signed integers.
            if loops:
                coeff = coords('z', len(loops))
                y = coords('y', self.rank)
                equations = []
                for i in range(self.rank):
                    rhs = ys[i]+''.join(f'{v[i]:+d}*{z}' for z, v in zip(coeff, loops) if v[i])
                    equations.append(y[i]+'='+rhs)
                branches.append(side(h, x)+' -> '+side(k, y)+' : exists ('+','.join(coeff)
                                +' : '+' and '.join(equations)+')')
            else:
                branches.append(side(h, x)+' -> '+side(k, ys))
        if not branches:
            either = side('h', x)
            return isl.Map('{ '+either+' -> '+either+' : false }')
        return isl.Map('{ '+'; '.join(branches)+' }').coalesce()

    def transports(self, e):
        pos = [next(i for i, (_, f) in enumerate(h) if f == e) for h in self.histories]
        center, offset, loops = {}, {}, defaultdict(set)
        gains = []
        for root in range(len(pos)):
            if root in center:
                continue
            center[root], offset[root] = root, self.zero
            todo = [root]
            while todo:
                h = todo.pop()
                for k, v in self.edges[h].values():
                    if pos[k] > pos[h]:
                        gains.append((h, k, v, ()))
                    if pos[k] != pos[h]:
                        continue
                    value = add(offset[h], v)
                    if k not in center:
                        center[k], offset[k] = root, value
                        todo.append(k)
                    cycle = add(value, neg(offset[k]))
                    if any(cycle):
                        loops[root].add(min(cycle, neg(cycle)))
        anchor = self.relation((h, c, neg(offset[h]), ()) for h, c in center.items())
        lattice = self.relation((c, c, self.zero, sorted(loops[c])) for c in set(center.values()))
        passive = anchor.apply_range(lattice).apply_range(anchor.reverse()).coalesce()
        gain = self.relation(gains).apply_range(passive)
        out = passive
        for _ in range(self.n-1):
            nxt = out.union(out.apply_range(gain)).coalesce()
            if nxt.is_equal(out):
                break
            out = nxt
        return out

    def decide(self, a, b):
        keys = tuple(a)
        pieces = []
        for m in keys:
            e, _ = m
            if e not in self.reachable:
                self.reachable[e] = self.transports(e)
            t = self.reachable[e]
            s, z = point(a[m]), point(b[m])
            interval = s.apply(t).intersect(z.apply(t.reverse()))
            if interval.is_empty():
                return False
            pieces.append(t.intersect_domain(interval).intersect_range(interval))
        if keys == tuple(b):
            return True
        motion = reduce(lambda s, t: s.flat_product(t), pieces).coalesce()
        start = point(tuple(x for m in keys for x in a[m])).apply(motion)
        target = point(tuple(x for m in keys for x in b[m]))
        goal = tuple(keys.index(m) for m in b)
        orders = {tuple(range(len(keys))): start}
        gains = sum(next(j for j, (_, e) in enumerate(self.histories[b[m][0]]) if e == m[0])
                    -next(j for j, (_, e) in enumerate(self.histories[a[m][0]]) if e == m[0]) for m in keys)
        limit = (gains+1)*len(keys)*(len(keys)-1)//2
        size = self.rank+1
        for _ in range(limit):
            new = dict(orders)
            for word, states in orders.items():
                for j, (x, y) in enumerate(zip(word, word[1:])):
                    if keys[x][0] == keys[y][0]:
                        continue
                    meet = states
                    for k in range(size):
                        meet = meet.equate(isl.dim_type.set, x*size+k, isl.dim_type.set, y*size+k)
                    if not meet.is_empty():
                        u = word[:j]+(y, x)+word[j+2:]
                        result = meet.apply(motion).coalesce()
                        if u == goal and not result.is_disjoint(target):
                            return True
                        new[u] = result if u not in new else new[u].union(result).coalesce()
            if new.keys() == orders.keys() and all(s.is_equal(orders[w]) for w, s in new.items()):
                break
            orders = new
        return False


def solve(data):
    first = winding(data)
    if first['obstruction']:
        return first
    model = Cover(data['history'], data['marks'])
    a, left = model.read(data['source'])
    b, right = model.read(data['target'])
    if left != right:
        return dict(surface_filler=False, obstruction='total braid')
    yes = model.decide(a, b)
    return dict(surface_filler=yes if model.abelian or not yes else None,
                cover_reachable=yes, abelian=model.abelian, rank=model.rank, histories=len(model.histories))


def checks():
    from semistrict_surface_acyclic_private_movies import Traces
    from semistrict_surface_private_simple_braid import read
    from semistrict_surface_private_histories import closure
    from semistrict_surface_private_braid_windows import factor, join
    from semistrict_surface_signed_private_model import Ball

    history = ((0, 's'), (0, 'u'), (0, 'd'))
    marks = {'s': [[], []], 'u': [[], ['f']], 'd': [['f'], []]}
    base = dict(edges={'f': [0, 0]}, initial=[], start_vertex=0, scalar_at={'s': 0},
                history=history, marks=marks, higher=[{'p'+op: [op, op] for op in marks}])
    model = Cover(history, marks)
    assert model.abelian and model.rank == 1
    graph = Ball(history, marks, 8)
    chart = Traces(marks, base['higher'][0], {})
    beta = (1, 2, 2, 1)*2
    # Put updates on the scalar and birth, in both orders, at old positive
    # prefixes of two complete circuits around the connected birth-death pair.
    examples = {}
    for a in range(0, 9, 2):
        for b in range(a, 9, 2):
            for events in ((0, 1), (1, 0)):
                w, order = [], list(range(3))
                for k in range(9):
                    for time, e in zip((a, b), events):
                        if time == k:
                            w.append(('p'+history[e][1], order.index(e)))
                    if k < len(beta):
                        i = beta[k]-1
                        w.append(('X', i))
                        order[i], order[i+1] = order[i+1], order[i]
                trace = read(chart, history, w)[2]
                word = graph.word(w, trace)
                examples[word] = model.read(w)[0], w
    total = positive = 0
    for source, (s, a) in examples.items():
        actual = closure(source, lambda w: (q for _, q in graph.steps(w)))
        for target, (t, b) in examples.items():
            yes = not winding(dict(base, source=a, target=b))['obstruction'] and model.decide(s, t)
            assert yes == (target in actual)
            total += 1
            positive += yes
    # Two scalar pairs at different gaps yield independent integral windings.
    spatial = dict(base, initial=['f'], history=[(1, 's')]*2+[(0, 's')]*2)
    sweep = [('X', i) for i in range(3)]
    tail = [('X', 1)]*6
    d = dict(spatial, source=[('ps', 0), ('ps', 1)]+sweep+tail,
             target=[('ps', 1)]+sweep+[('ps', 3)]+tail)
    out = solve(d)
    assert out['surface_filler'] and out['rank'] == 2
    from semistrict_surface_private_heap_order import solve as raw
    def crossings(path):
        return [('X', i-1) for i in path]
    failure = dict(spatial, source=[('ps', 0)]+crossings((2, 1, 2, 3, 2, 1, 1)),
                   target=crossings((1, 2, 1, 3))+[('ps', 3)]+crossings((2, 1, 1)))
    assert solve(failure)['surface_filler'] and not raw(failure)['raw_filler']
    # Noncommuting pure loops with equal homology coordinates. The positive
    # projection in this case cannot decide the actual stationary comparison.
    a, b = (1, 1, 2, 2), (2, 2, 1, 1)
    beta = join(a, b)
    def marked(prefix):
        return [('X', i-1) for i in prefix]+[('ps', 1)]+[('X', i-1) for i in factor(prefix, beta)]
    nonabelian = dict(base, history=[(0, 's')]*3, source=marked(a), target=marked(b))
    out = solve(nonabelian)
    assert out['cover_reachable'] and out['surface_filler'] is None and not out['abelian']
    print(f'{total} positioned birth-death comparisons agree with direct signed search '
          f'({positive} inhabited); independent rank-two windings and a nonabelian loss checked.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces', type=Path)
    args = parser.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()))))
    else:
        checks()
