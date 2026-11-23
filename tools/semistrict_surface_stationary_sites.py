"""Decide raw and simultaneous reflection for unchanged temporal site order (islpy).

Inputs use semistrict_surface_scalar_sites' JSON format. --all tests every old
positive pair at precisely the query's named temporal source and target.
"""
import argparse
import json
from itertools import count, product
from pathlib import Path

import islpy as isl

from semistrict_surface_scalar_sites import Faces, evaluate, profile_example


def variables(prefix, n):
    return [prefix+str(i) for i in range(n)]


def coords(names):
    return '['+', '.join(names)+']'


def linear(coeffs, names):
    return ' + '.join(f'{a}*{x}' for a, x in zip(coeffs,names) if a) or '0'


def region(names, constraints):
    condition = ' : '+' and '.join(constraints) if constraints else ''
    return isl.Set('{ '+coords(names)+condition+' }')


def nonnegative(names):
    return [x+' >= 0' for x in names]


def monoid_region(names, base, periods, expressions=None):
    """Vectors in a linear set, optionally pulled back by integer expressions."""
    coefficients = variables('c', len(periods))
    exprs = names if expressions is None else expressions
    eqs = [f'{x} = {b} + '+linear([row[i] for row in periods], coefficients)
           for i,(x,b) in enumerate(zip(exprs,base))]
    if not coefficients:
        return region(names, eqs)
    body = ' and '.join(nonnegative(coefficients)+eqs)
    return region(names, ['exists ('+', '.join(coefficients)+': '+body+')'])


def decode_union(bits, d):
    """Unary length-delimited finite lists of linear sets in N^d."""
    if not bits.endswith('0'):
        return None
    vals = [len(v) for v in bits[:-1].split('0')]
    pos, parts = 0, []
    while pos < len(vals):
        size = vals[pos]
        pos += 1
        end = pos+(size+1)*d
        if end > len(vals):
            return None
        vectors = [tuple(vals[i:i+d]) for i in range(pos, end, d)]
        parts.append((vectors[0], vectors[1:]))
        pos = end
    return parts


def step(v, edges):
    for a, b in edges:
        if all(x >= need for x, need in zip(v,a)):
            yield tuple(x-need+give for x,need,give in zip(v,a,b))


def petri(start, goal, edges):
    if start == goal:
        return True
    d = len(start)
    names, dest = variables('x', d), variables('y', d)
    source, target = (monoid_region(names, v, []) for v in (start,goal))
    maps = []
    for a,b in edges:
        conds = [f'{x} >= {m} and {y} = {x} + ({n-m})' for x,y,m,n in zip(names,dest,a,b)]
        maps.append(isl.Map('{ '+coords(names)+' -> '+coords(dest)+' : '+' and '.join(conds)+' }'))
    reverse = [(b,a) for a,b in edges]
    seen, back = {start}, {goal}
    frontier, following = {start}, {goal}
    for size in count(1):
        frontier = {w for v in frontier for w in step(v, edges)} - seen
        if frontier & back:
            return True
        seen.update(frontier)
        following = {w for v in following for w in step(v, reverse)} - back
        if following & seen:
            return True
        if not frontier or not following:
            return False
        back.update(following)
        parts = decode_union(bin(size)[3:], d)
        if parts:
            candidate = region(names, ['0 = 1'])
            for base, periods in parts:
                candidate = candidate.union(monoid_region(names, base, periods))
            if (source.is_subset(candidate) and target.is_disjoint(candidate)
                    and all(candidate.apply(m).is_subset(candidate) for m in maps)):
                return False


class Stationary:
    def __init__(self, data):
        def faces(e):
            return Faces(e, data['edges'], data['scalars'])
        q = faces(data['query'])
        if q.crowded or [p for p,_ in q.history] != [p for p,_ in q.end]:
            raise ValueError('query needs unchanged site order with at most two events per site')
        spots = sorted((s,i) for i, ((s,_),(t,_)) in enumerate(zip(q.history,q.history[1:])) if s == t)
        self.active = {site: j for j,(site,_) in enumerate(spots)}
        self.scale = [1 if q.history[i] == q.history[i+1] else 2 for _,i in spots]
        self.offset = [int(q.history[i] != q.end[i]) for _,i in spots]
        self.ambient = q.sites
        self.endpoints = tuple(tuple((counts[q.sites.index(s)]-self.offset[j])//self.scale[j]
                                     for j,(s,_) in enumerate(spots)) for counts in q.counts)
        rows, edges = set(), set()
        for rule in map(faces,data['rules']):
            rows.update(q.placements(rule))
            if rule.crowded or [p for p,_ in rule.history] != [p for p,_ in rule.end]:
                continue
            for shift in range(len(q.path)-len(rule.path)+1):
                if q.vertices[shift] != rule.vertices[0] or q.path[shift:shift+len(rule.path)] != rule.path:
                    continue
                h = tuple((s+shift,c) for s,c in rule.history)
                for phase in product(*(range(k) for k in self.scale)):
                    order = list(q.history)
                    for bit, (_,i) in zip(phase,spots):
                        if bit:
                            order[i],order[i+1] = order[i+1],order[i]
                    if not any(tuple(order[i:i+len(h)]) == h for i in range(len(order)-len(h)+1)):
                        continue
                    left, right = (dict(zip((s+shift for s in rule.sites), v)) for v in rule.counts)
                    need, give = [], []
                    for j,(s,_) in enumerate(spots):
                        a,b = left.get(s,0),right.get(s,0)
                        k = self.scale[j]
                        minimal = max(0,(phase[j]+a-self.offset[j]+k-1)//k)
                        assert (b-a)%k == 0
                        need.append(minimal)
                        give.append(minimal+(b-a)//k)
                    edges.add((tuple(need),tuple(give)))
        self.rows = sorted(v for v in rows if any(v))
        self.edges = sorted((a,b) for a,b in edges if a != b)

    def failure(self):
        d = len(self.scale)
        if d == 0:
            return None
        names = variables('x',d)
        zero = monoid_region(names,(0,)*d,[])
        for sign in product((1,-1),repeat=d):
            exprs = [f'{sign[j]*self.scale[j]}*{names[j]}' if (j:=self.active.get(s)) is not None else '0'
                     for s in self.ambient]
            cone = monoid_region(names,(0,)*len(exprs),self.rows,exprs).intersect(region(names,nonnegative(names)))
            positive = cone.subtract(zero)
            atoms = positive.subtract(positive.sum(positive))
            vectors = []
            atoms.foreach_point(lambda p: vectors.append(tuple(
                p.get_coordinate_val(isl.dim_type.set,i).to_python() for i in range(d))))
            for v in vectors:
                diff = tuple(x*s for x,s in zip(v,sign))
                pair = tuple(tuple(max(0,t*x) for x in diff) for t in (-1,1))
                if not petri(*pair,self.edges):
                    return tuple(tuple(s*x+r for s,x,r in zip(self.scale,v,self.offset)) for v in pair)
        return None


def checks():
    total = 0
    for rows in ([(1,1)], [(2,-1),(-1,2)], [(1,0),(0,1)], [(1,1),(-2,-2)], []):
        for end in product(range(3),repeat=2):
            m = Stationary(profile_example(2,rows,end))
            assert set(m.edges) == {(tuple(max(0,-v) for v in row),tuple(max(0,v) for v in row)) for row in rows}
            result = petri(*m.endpoints,m.edges)
            if rows == [(1,1)] or rows == [(1,1),(-2,-2)]:
                expected = end[0] == end[1]
            elif rows == [(1,0),(0,1)]:
                expected = True
            else:
                expected = end == (0,0)
            assert result == expected
            total += 1
    # Withdrawing and depositing across two sites separately needs tokens.
    # Both primitive signed changes are already minimally enabled, but their
    # combination (1,1) cannot start at the empty marking.
    m = Stationary(profile_example(2,[(2,-1),(-1,2)],(1,1)))
    f = m.failure()
    assert f is not None and not petri(*f,m.edges)
    assert Stationary(profile_example(2,[(1,1)],(2,2))).failure() is None
    # Named phases: a B,A rule cannot fire at count zero on A,B. At odd
    # endpoints the incoming crossing places it at its required phase.
    base = dict(edges={},scalars={'A':'v','B':'v'})
    base['rules'] = [dict(root='v',path=[],history=[(0,'B'),(0,'A')],left=[],right=[1,1])]
    for end,expect in (([1,1],False),([1,1,1],True)):
        lhs = [] if len(end) == 2 else [1]
        base['query'] = dict(root='v',path=[],history=[(0,'A'),(0,'B')],left=lhs,right=end)
        m = Stationary(base)
        assert petri(*m.endpoints,m.edges) == expect
        assert (m.failure() is None) == expect
    # Compare minimal prefix-phase guards with every literal spelling and
    # occurrence, including opposite orders at just one of the sites.
    sources = ('AABB','ABAB','ABBA')
    direct = 0
    for labels, shift in product(sources,(0,1)):
        h = tuple((i//2, name) for i,name in enumerate(labels))
        data = dict(edges={'f':('v','v')},scalars={'A':'v','B':'v'})
        block = h[2*shift:2*shift+2]
        for order in (block,block[::-1]):
            rule = dict(root='v',path=[],history=[(0,c) for _,c in order],left=[],right=[1,1])
            data['rules'] = [rule]
            groups = {}
            for length in range(5):
                for w in product((1,3),repeat=length):
                    end,mark = evaluate(h,w)
                    groups.setdefault((end,mark),[]).append(w)
            for (_,mark), words in groups.items():
                data['query'] = dict(root='v',path=['f'],history=h,left=words[0],right=words[0])
                model = Stationary(data)
                state = model.endpoints[0]
                actual = set()
                for word in words:
                    for pos in range(len(word)+1):
                        before,_ = evaluate(h,word[:pos])
                        for j in (0,2):
                            if tuple(c for _,c in before[j:j+2]) == tuple(c for _,c in order):
                                out = word[:pos]+(j+1,j+1)+word[pos:]
                                actual.add(evaluate(h,out)[1])
                compiled = {tuple(k*x+t for k,x,t in zip(model.scale,next_mark,model.offset))
                            for next_mark in step(state,model.edges)}
                assert actual == compiled
                direct += 1
    print(f'{total} Petri judgments, {direct} literal successor sets, joint orthant and named parity tests passed')


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--presentation',type=Path)
    ap.add_argument('--all',action='store_true')
    args = ap.parse_args()
    if args.presentation:
        model = Stationary(json.loads(args.presentation.read_text()))
        if args.all:
            print('missing positive count pair',model.failure())
        else:
            print('raw',petri(*model.endpoints,model.edges))
    else:
        checks()
