"""Necessary temporal windows for a last late triangle and an early inner exchange.

On the seven strands of their disjoint supports, delete all but the triangle
and two of the quartet. A carrier on a return must be in the same strongly
connected component as a carrier in the original late half. After a last late
triangle only early triangles may occur on the rest of its 4-route to the
fixed outside 3-target. Compare the intermediate 2-state between the inverted
windows on all six projections, also imposing per-strand incidence order.
"""

from collections import Counter
from functools import cache
from itertools import combinations, permutations

from interchange_sorting_fiber import raw_histories
from interchange_triangle_carriers import (
    BIT, PACKETS, START, TRIPLES, components, orientation, trajectory,
)
from interchange_triangle_join_interval import gray, ground_interval, restrict_interval


@cache
def after_states(cut, mark):
    early = increasing(cut)
    assert PACKETS[mark].isdisjoint(early)
    mono = {t for t in TRIPLES if PACKETS[t].isdisjoint(early) or PACKETS[t] <= early}
    histories = set(raw_histories(START))
    outside = {p for p in histories if cut in trajectory(p)}
    sources = {p for p in outside if not orientation(p) & BIT[mark]}
    targets = {p for p in outside if orientation(p) & BIT[mark]}
    classes, at = restrict_interval(START, sources, targets, histories,
                                    lambda e: e.family == 'K15' or set(gray(e)) <= mono)
    graph, labels = ground_interval(classes, at)
    scc = components(graph, labels, mark)
    original = {scc[n] for e, n in labels.items() if n in scc and
                e.source in outside and e.lo >= len(early)}
    # After the marked edge the 4-path still has to reach an outside
    # 3-target without performing another late triangle.
    tail, _ = restrict_interval(START, classes.keys(), targets, classes.keys(),
                                lambda e: e.family == 'K15' or
                                all(PACKETS[t] <= early for t in gray(e)))
    return frozenset(state for e, n in labels.items()
                     if n in scc and scc[n] in original and e.target in tail
                     for state in trajectory(e.source)[e.hi:])


def increasing(state):
    return frozenset(a+b for a, b in combinations(state, 2) if a < b)


def normalize(word, strands):
    rename = str.maketrans(''.join(sorted(strands)), 'abcde')
    return ''.join(x for x in word if x in strands).translate(rename)


def matchings(quartet, early):
    for x in quartet[1:]:
        a = quartet[0] + x
        b = ''.join(y for y in quartet if y not in a)
        if {a, b} <= early:
            yield a, b


def compatible_split(split, matching):
    left, right = matching
    return (max(map(split.index, left)) < min(map(split.index, right)) or
            max(map(split.index, right)) < min(map(split.index, left)))


def candidate_windows(cut, triangle, quartet, middles):
    early = increasing(cut)
    candidates = list(matchings(quartet, early))
    if not candidates:
        return candidates, set()
    views = {}
    pending = set(candidates)
    for pair in combinations(quartet, 2):
        strands = triangle + ''.join(pair)
        states = after_states(normalize(cut, strands), normalize(triangle, strands))
        views[strands] = states
        # Pending pairs must still be descending at the intermediate 2-state.
        if all(s.index(normalize(pair[0], strands)) < s.index(normalize(pair[1], strands))
               for s in states):
            pending = {m for m in pending if ''.join(pair) not in m}
            if not pending:
                return candidates, set()
    surviving = set()
    for split, done in middles:
        # An unfinished early crossing and a completed late crossing cannot
        # share a strand. Otherwise their incidences would be out of order.
        if set(''.join(early - done)) & set(''.join(done - early)):
            continue
        possible = {p for p in pending if set(p).isdisjoint(done) and compatible_split(split, p)}
        if possible and all(normalize(split, strands) in allowed for strands, allowed in views.items()):
            surviving.update(possible)
    return candidates, surviving


def cases():
    words = [''.join(p) for p in permutations('abcdefg')]
    done = {w: increasing(w) for w in words}
    for triple in combinations('abcdefg', 3):
        triangle = ''.join(triple)
        quartet = ''.join(x for x in 'abcdefg' if x not in triangle)
        middles = [(w, done[w]) for w in words if ''.join(x for x in w if x in triple) == triangle]
        for middle, _ in middles:
            cut = middle.translate(str.maketrans(triangle, triangle[::-1]))
            possible, surviving = candidate_windows(cut, triangle, quartet, middles)
            if possible:
                yield cut, triangle, quartet, possible, surviving


def check():
    counts = Counter()
    for cut, triangle, quartet, possible, surviving in cases():
        counts['placements'] += 1
        counts['matchings'] += len(possible)
        counts['surviving placements'] += bool(surviving)
        counts['surviving matchings'] += len(surviving)
        if surviving:
            assert cut.endswith(triangle[::-1])
    assert counts == {'placements': 14700, 'matchings': 22050,
                      'surviving placements': 168, 'surviving matchings': 216}
    print(dict(counts))


if __name__ == '__main__':
    check()
