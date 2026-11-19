"""Project a separated degree-five boundary to each four-strand sorting interval."""

from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, permutations

from interchange_sorting_fiber import moves, raw_histories, states


START = 'dcba'
HISTORIES = raw_histories(START)
ARROWS = tuple(g for p in HISTORIES for g in moves(START, p))
PAIRS = tuple(''.join(p) for p in combinations('abcd', 2))


@cache
def triangles(g):
    if g.family in ('r', 'h'):
        moving, stationary = g.right_events, g.left
    elif g.family == 't':
        moving, stationary = g.left_events, g.right
    else:
        return frozenset()
    return frozenset(''.join(sorted(e+y)) for e in moving for y in stationary)


def excess(g, early):
    """The quartet's unfiltered weight less the two single-color weights."""
    if g.family == 'K15':
        return 0
    if g.family == 'i':
        return sum((e in early) != (f in early)
                   for e in g.left_events for f in g.right_events)
    if g.family == 't':
        slots, events, outside, sign = g.left, g.left_events, g.right, -1
    else:
        slots, events, outside, sign = g.right, g.right_events, g.left, 1
    total = 0
    for state, e in zip(states(slots, events), events):
        i = state.index(e[1])
        assert state[i:i+2] == e[::-1]
        for j, z in enumerate(state):
            if z in e:
                continue
            for y in outside:
                spectator = ''.join(sorted((y, z)))
                if (spectator in early) != (e in early):
                    total += sign if j > i else -sign
    if g.family == 'h':
        total -= sum((e in early) != (f in early)
                     for e in g.right_events for f in g.left_events)
    return total


def closure(seeds, edges, backwards=False):
    graph = defaultdict(set)
    for g in edges:
        src, dst = (g.target, g.source) if backwards else (g.source, g.target)
        graph[src].add(dst)
    seen = set(seeds)
    pending = list(seeds)
    while pending:
        for dst in graph[pending.pop()] - seen:
            seen.add(dst)
            pending.append(dst)
    return seen


def triangle_color(t, early):
    return {''.join(p) in early for p in combinations(t, 2)}


def local_test(cut):
    early = frozenset(p for p in PAIRS if cut.index(p[0]) < cut.index(p[1]))
    seeds = {raw for raw in HISTORIES if cut in states(START, raw)}
    allowed = [g for g in ARROWS if all(len(triangle_color(t, early)) == 1
                                        for t in triangles(g))]
    early_only = [g for g in allowed if all(triangle_color(t, early) == {True}
                                             for t in triangles(g))]
    forward = closure(seeds, early_only)
    backward = closure(seeds, early_only, backwards=True)
    fringe = []
    for g in early_only:
        if g.source not in forward or g.target not in backward:
            continue
        score = excess(g, early)
        assert score >= 0
        if triangles(g) and any(e not in early for e in g.source[g.lo:g.hi]):
            assert score > 0
            fringe.append(g)

    # A positive inner edge spends one unit for each opposite-color pair.
    # Negative mixed contributions spend distinct triangles in a 4-path.
    packing = {frozenset(): 0}
    negative = {(triangles(g), -excess(g, early)) for g in allowed
                if excess(g, early) < 0}
    for support, credit in negative:
        assert support
        for used, score in list(packing.items()):
            if used.isdisjoint(support):
                union = used | support
                packing[union] = max(packing.get(union, 0), score+credit)
    assert max(packing.values()) <= 1

    # Retain every complete 4-route between two cut-compatible histories
    # with zero excess. Loops with zero excess need no length cutoff.
    initial = [(raw, frozenset(), 0, None) for raw in seeds]
    seen = set(initial)
    pending = list(initial)
    hits = set()
    outgoing = defaultdict(list)
    for g in allowed:
        outgoing[g.source].append(g)
    while pending:
        raw, used, total, mark = pending.pop()
        if raw in seeds and total == 0 and mark is not None:
            hits.add((mark, tuple(sorted(used))))
        for g in outgoing[raw]:
            support = triangles(g)
            if used & support:
                continue
            step = excess(g, early)
            next_mark = mark
            if g.family == 'i' and step:
                # Packing proved that every zero-excess route uses at most one.
                if mark is not None:
                    continue
                assert step == 1 and len(g.left_events) == len(g.right_events) == 1
                next_mark = (tuple(sorted(g.left_events + g.right_events)),
                             tuple(sorted(used)), g.left_events[0])
            node = (g.target, used | support, total+step, next_mark)
            if node not in seen:
                seen.add(node)
                pending.append(node)
    return fringe, hits


# (opposite pair, triangle support already traversed, spatially left event),
# followed by the total triangle support of the accepted 4-route.
EXPECTED = {
    'adcb': {((('ad','bc'), ('bcd',), 'ad'), ('bcd',))},
    'bdca': {((('ac','bd'), ('acd',), 'bd'), ('acd',))},
    'cbad': {((('ad','bc'), (), 'bc'), ('abc',))},
    'cdba': {((('ab','cd'), ('abc','abd'), 'cd'), ('abc','abd')),
             ((('ab','cd'), ('abd',), 'cd'), ('abd',))},
    'dbac': {((('ac','bd'), (), 'bd'), ('abd',))},
    'dcab': {((('ab','cd'), (), 'cd'), ('acd',)),
             ((('ab','cd'), (), 'cd'), ('acd','bcd'))},
}


@cache
def eligible_quartet(values):
    order = sorted(values)
    return ''.join('abcd'[order.index(v)] for v in values) in EXPECTED


def check():
    assert len(HISTORIES) == 16
    assert Counter(g.family for g in ARROWS) == {'i':10, 'r':28, 't':28, 'h':4, 'K15':12}
    fringe = Counter()
    for w in permutations('abcd'):
        cut = ''.join(w)
        exceptional, hits = local_test(cut)
        assert hits == EXPECTED.get(cut, set())
        for ((opposite, before, left), all_triangles) in hits:
            early = {p for p in PAIRS if cut.index(p[0]) < cut.index(p[1])}
            if left not in early:
                right = next(p for p in opposite if p != left)
                u = min(right)
                required = ''.join(sorted(left + u))
                assert u < min(left) and required in all_triangles and required not in before
                assert triangle_color(required, early) == {False}
        for g in exceptional:
            fringe[(cut, g.family)] += 1
    assert fringe == {('acdb','r'):1, ('bcda','r'):1, ('cabd','t'):1, ('dabc','t'):1}
    print('Verified the early-window inequality at all 24 cuts on 16 histories and 82 arrows.')
    print('Six cut patterns allow an opposite-color inner pair; each requires a late triangle.')
    scores = Counter(sum(eligible_quartet(q) for q in combinations(w, 4))
                     for w in permutations(range(8)))
    assert sum(scores.values()) == 40320 and max(scores) == 45 and scores[45] == 2
    print('At most 45 eligible quartets on eight strands; two cuts attain this pattern count.')


if __name__ == '__main__':
    check()
