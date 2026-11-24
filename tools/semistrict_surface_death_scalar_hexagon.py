"""Compute named exchange charts and their hexagons around a two-wire death."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, permutations
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity

WORDS = {'L': ('ab', 'ab'), 'R': ('cd', 'cd'), 'X': ('', ''), '!': ('bc', '')}
ENDS = {'a': (0, 1), 'b': (1, 2), 'c': (2, 1), 'd': (1, 3)}
NAMES = frozenset('LRX')


def schedules(word, remaining, start_vertex):
    if not remaining:
        yield ()
    for g in remaining:
        source, target = WORDS[g]
        for i in range(len(word)+1-len(source)):
            if not word.startswith(source, i):
                continue
            if g == 'X' and (start_vertex if i == 0 else ENDS[word[i-1]][1]) != 1:
                continue
            for tail in schedules(word[:i]+target+word[i+len(source):], remaining-{g}, start_vertex):
                yield ((g, i),) + tail


def swaps(h):
    for k, ((a, i), (b, j)) in enumerate(zip(h, h[1:])):
        m, n = map(len, WORDS[a])
        p, q = map(len, WORDS[b])
        if j+p <= i:
            yield h[:k] + ((b, j), (a, i+q-p)) + h[k+2:]
        if i+n <= j:
            yield h[:k] + ((b, j-n+m), (a, i)) + h[k+2:]


def common_row(h):
    place = next(i for i, (g, _) in enumerate(h) if g == '!')
    if place not in (0, len(h)-1):
        return False
    blocks = [(i, i+len(WORDS[g][0])) for g, i in h if g != '!']
    return all(b <= c or d <= a for (a, b), (c, d) in combinations(blocks, 2))


@cache
def charts(names, word='abcd'):
    todo = set(schedules(word, names | {'!'}, ENDS[word[0]][0]))
    components = {}
    outer = set()
    while todo:
        start = min(todo)
        todo.remove(start)
        queue = [start]
        while queue:
            h = queue.pop()
            components[h] = start
            if common_row(h):
                outer.add(start)
            for nxt in swaps(h):
                if nxt in todo:
                    todo.remove(nxt)
                    queue.append(nxt)
                else:
                    assert nxt in components or nxt in queue
    return components, outer


def restrict(h, names):
    return tuple((g,i) for g,i in h if g == '!' or g in names)


def edge(order, i, chart):
    switched = order[:i] + (order[i+1], order[i]) + order[i+2:]
    return min(order, switched), max(order, switched), chart


def audit():
    orders = list(permutations(sorted(NAMES)))
    edges = set()
    outer_edges = set()
    for order in orders:
        for i in (0, 1):
            names = frozenset(order[i:i+2])
            charts_at_pair, outer = charts(names)
            edges.update(edge(order, i, c) for c in set(charts_at_pair.values()))
            outer_edges.update(edge(order, i, c) for c in outer)
    full, outer = charts(NAMES)
    assert not outer
    hexagons = []
    for chart in sorted(set(full.values())):
        boundary = set()
        for order in orders:
            for i in (0, 1):
                names = frozenset(order[i:i+2])
                image = charts(names)[0][restrict(chart, names)]
                boundary.add(edge(order, i, image))
        assert len(boundary) == 6 and boundary <= edges
        hexagons.append(boundary)
    assert len(hexagons) == 3 and hexagons.count(outer_edges) == 1
    sizes = sorted(len(h-outer_edges) for h in hexagons)
    assert sizes == [0, 2, 2]
    work = set(edges)
    while hexagons:
        counts = Counter(e for h in hexagons for e in h)
        private = next(e for e in counts if counts[e] == 1)
        work.remove(private)
        hexagons.remove(next(h for h in hexagons if private in h))
    adj = defaultdict(set)
    for u, v_, _ in work:
        adj[u].add(v_)
        adj[v_].add(u)
    seen = set()
    stack = [orders[0]]
    while stack:
        u = stack.pop()
        if u not in seen:
            seen.add(u)
            stack.extend(adj[u]-seen)
    assert seen == set(orders) and len(work)-len(seen)+1 == 2
    # Exhaust all divisors containing the death for the low-grade surface model.
    for word in ('bc','abc','bcd','abcd'):
        available = sorted(n for n in NAMES if WORDS[n][0] in word)
        for name in available:
            single, _ = charts(frozenset((name,)), word)
            assert len(set(single.values())) == 1
        for a, b in combinations(available, 2):
            actual, outer = charts(frozenset((a,b)), word)
            assert len(outer) <= 1 and actual
    print('serial vertices', len(orders), 'edges', len(edges), 'outer edges', len(outer_edges))
    print('full hexagons with 0, 1, 2 dependent boundary edges:', [sizes.count(k) for k in range(3)])
    print('common-row triples', len(charts(NAMES)[1]), 'graph after collapses:', len(seen), 'vertices,',
          len(work), 'edges, free rank', len(work)-len(seen)+1)


def typed(directory):
    ctx = (STAR,)*4 + tuple(arr(STAR, v(s), v(t)) for s,t in ENDS.values())
    a,b,c,d = map(v, range(4,8))
    unit = identity(ctx,v(1))
    death = arr(infer(ctx,unit), comp2(ctx,0,b,c), unit)
    ctx += (death,)
    poles = [identity(ctx,comp2(ctx,0,a,b)), identity(ctx,comp2(ctx,0,c,d)), identity(ctx,unit)]
    ctx += tuple(arr(infer(ctx,p),p,p) for p in poles)
    check_ctx(ctx)
    cell = comp2(ctx,0,comp2(ctx,0,a,v(8)),d)
    if directory:
        e = Emitter()
        for k,name in enumerate(('death','left','right','point'), start=8):
            e.check_type(name,ctx,v(k),ctx[k])
        e.check_type('stationaryDiagram',ctx,cell,infer(ctx,cell))
        g = e.ctx(ctx)
        e.checks.append(f'typed : {g} ⊢ctx\ntyped = from-just (checkCtx {g})\n')
        (directory / 'DeathScalarHexagon.agda').write_text(e.module('DeathScalarHexagon',__doc__))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    typed(args.agda_dir)
    audit()
