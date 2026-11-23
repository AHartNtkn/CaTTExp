"""Degree-four surface decision on scalar sites of a fixed edge path (islpy).

Input JSON has edges {name:[source,target]}, scalars {name:vertex}, query
and rules. Each face pair has root, path (edge names), history ([site,name]
events) and left/right positive words (lists of one-based swap positions).
"""
import argparse
import json
from collections import Counter
from itertools import combinations, permutations, product
from pathlib import Path

import islpy as isl


def evaluate(history, word, signed=False):
    profile = Counter(i for i, _ in history)
    counts = Counter()
    h = list(history)
    for letter in word:
        i = abs(letter)-1
        if not 0 <= i < len(h)-1 or (not signed and letter < 0):
            raise ValueError('invalid crossing position or sign')
        a, b = h[i:i+2]
        if (letter > 0 and a[0] < b[0]) or (letter < 0 and a[0] > b[0]):
            raise ValueError('crossing has the wrong spatial orientation')
        if a[0] == b[0]:
            counts[a[0]] += 1 if letter > 0 else -1
        h[i:i+2] = [b, a]
    return tuple(h), tuple(counts[i] for i in sorted(profile) if profile[i] >= 2)


class Faces:
    def __init__(self, data, edges, scalars):
        self.path = tuple(data['path'])
        self.vertices = [data['root']]
        for edge in self.path:
            start, end = edges[edge]
            if start != self.vertices[-1]:
                raise ValueError('edges do not form a path')
            self.vertices.append(end)
        hist = tuple(tuple(v) for v in data['history'])
        if any(not 0 <= slot < len(self.vertices) or scalars[name] != self.vertices[slot]
               for slot, name in hist):
            raise ValueError('scalar at the wrong site')
        self.history = hist
        self.profile = Counter(hist)
        multiplicities = Counter(slot for slot, _ in hist)
        self.sites = [s for s, m in sorted(multiplicities.items()) if m >= 2]
        self.crowded = any(m > 2 for m in multiplicities.values())
        (u, a), (v, b) = (evaluate(hist, data[side]) for side in ('left', 'right'))
        if u != v:
            raise ValueError('crossing faces must have the same temporal endpoint')
        self.end = u
        self.counts = a, b
        self.defect = tuple(y-x for x, y in zip(a, b))

    def placements(self, rule):
        for shift in range(len(self.path)-len(rule.path)+1):
            if (self.vertices[shift] != rule.vertices[0]
                    or self.path[shift:shift+len(rule.path)] != rule.path):
                continue
            if all(self.profile[(shift+i, name)] >= count for (i, name), count in rule.profile.items()):
                by_site = dict(zip((shift+i for i in rule.sites), rule.defect))
                yield tuple(by_site.get(i, 0) for i in self.sites)


def coefficients(rows, target):
    if not any(target):
        return [0]*len(rows)
    if not rows:
        return None
    names = [f'x{i}' for i in range(len(rows))]
    conditions = [f'{x} >= 0' for x in names]
    for j, value in enumerate(target):
        expression = ' + '.join(f'{row[j]}*{x}' for row, x in zip(rows, names) if row[j]) or '0'
        conditions.append(expression+' = '+str(value))
    system = isl.Set('{ ['+', '.join(names)+'] : '+' and '.join(conditions)+' }')
    if system.is_empty():
        return None
    point = system.sample_point()
    solution = [point.get_coordinate_val(isl.dim_type.set, i).to_python() for i in range(len(rows))]
    assert all(x >= 0 for x in solution)
    assert tuple(sum(row[j]*x for row, x in zip(rows, solution)) for j in range(len(target))) == target
    return solution


def decide(data):
    def faces(entry):
        return Faces(entry, data['edges'], data['scalars'])
    q = faces(data['query'])
    if q.crowded:
        raise ValueError('this decision requires at most two scalar events at each queried site')
    rows = sorted({v for entry in data['rules'] for v in q.placements(faces(entry)) if any(v)})
    return q.defect, rows, coefficients(rows, q.defect)


def exchange_checks():
    # Independent comparison: Artin action on all strands detects equality of
    # signed histories before any declaration. Check injectivity on the proposed
    # tuple coordinates at fixed endpoints, including opposite crossing signs.
    from semistrict_surface_shared_edge import braid_image
    count = 0
    for sites in ((0, 0, 1, 1), (0, 1, 1, 2), (0, 0, 1)):
        for h in sorted(set(permutations(tuple((s, 'a') for s in sites)))):
            by_tuple, by_braid = {}, {}
            todo = [((), h)]
            for _ in range(5):
                following = []
                for w, end in todo:
                    key = evaluate(h, w, signed=True)
                    whole = end, braid_image(len(h), w)
                    assert by_tuple.setdefault(key, whole) == whole
                    assert by_braid.setdefault(whole, key) == key
                    count += 1
                    for i in range(len(h)-1):
                        for sign in (1, -1):
                            if sign*(end[i][0]-end[i+1][0]) >= 0:
                                v = end[:i]+(end[i+1], end[i])+end[i+2:]
                                following.append((w+(sign*(i+1),), v))
                todo = following
    return count


def profile_example(d, columns, target, reversed_sites=False):
    edges = {str(i): [i, i+1] for i in range(d-1)}
    names = {str(i): i for i in range(d)}
    def faces(col, rev=False):
        sites = list(range(d))[::-1] if rev else list(range(d))
        def word(sign):
            return [2*j+1 for j, i in enumerate(sites) for _ in range(max(0, sign*col[i]))]
        return dict(root=0, path=list(edges), history=[(i, str(i)) for i in sites for _ in range(2)],
                    left=word(-1), right=word(1))
    return dict(edges=edges, scalars=names, query=faces(target, reversed_sites),
                rules=[faces(col) for col in columns])


def checks():
    count = exchange_checks()
    positive = profile_example(2, [(2, 2)], (2, 2), True)
    assert decide(positive)[2] == [1]
    assert decide(profile_example(2, [(2, 2)], (2, 0), True))[2] is None
    signed = profile_example(3, [(2,-1,0), (-1,0,-2)], (3,-2,-2))
    assert decide(signed)[2] is not None
    # A rule at a single vertex can be placed twice along the same loop path.
    loop = dict(edges={'f': ['x','x']}, scalars={'a':'x'})
    loop['rules'] = [dict(root='x', path=[], history=[(0,'a')]*2, left=[], right=[1,1])]
    loop['query'] = dict(root='x', path=['f'], history=[(0,'a')]*2+[(1,'a')]*2,
                         left=[], right=[1,1,3,3])
    assert decide(loop) == ((2,2), [(0,2),(2,0)], [1,1])
    triples = list(combinations(range(6), 3))
    for a,b in product(triples, repeat=2):
        rows = [tuple(int(i in s) for i in range(6)) for s in (a,b)]
        assert (decide(profile_example(6, rows, (1,)*6))[2] is not None) == set(a).isdisjoint(b)
    print(f'{count} signed histories, 400 exact-cover presentations, mixed signs and repeated path sites checked')


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--presentation', type=Path)
    args = ap.parse_args()
    if args.presentation:
        print('target, generators, integer witness', decide(json.loads(args.presentation.read_text())))
    else:
        checks()
