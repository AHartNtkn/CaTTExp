"""Five-strand obstructions to an outer edge carrying two disjoint marks.

Keep the four varying strands and one stationary strand x of a proposed
six-strand double edge. Its two marked crossings g and f survive, and the
common-slot triangles gx (early) and fx (late) both flip. At both exterior
schedules fx occurs before gx. The common-slot pin proved in the note forces
this order on every presentation on a return cycle. Hence no intermediate
3-history can have gx flipped while fx is still unflipped. In a simultaneous
edge the common-slot reading must be fx,gx, chronological for r and reverse
chronological for t. A six-strand join specializes to r on this projection.

The finite graph below allows all monochromatic triangles, all inner moves
and all block equations between the permitted histories. Each table of 0/1
edge scores is zero on every edge in either original temporal interval. The
sum is equal under equations, weakly increasing on directed comparisons, and
positive on every eligible simultaneous edge. A cycle through either original
schedule stays at score zero. This works for arbitrarily long 4-paths.

A separate score on the interval of Response 25 strictly decreases at each
H_R that could increase a shared-slot inversion count. A projection retaining
the two slots of its left varying crossing and the early right-hand triangle
has exactly that five-strand early/late partition. This rules the step out
on any cycle before applying the common-slot pin above.
"""
from itertools import combinations

from interchange_regular_rectangles import Rank, verify_rank
from interchange_sorting_fiber import raw_histories
from interchange_triangle_join_interval import START, gray, ground, ground_interval, restrict_interval


# Labels are assigned by ground_interval's sorted endpoint/edge signatures.
DOUBLE_SCORES = {
    ('r', 'ad'): (10, 11, 12, 13, 26, 89, 94),
    ('r', 'bd'): (19, 20, 21, 28, 29, 30, 38, 39, 40, 41, 57, 64, 71, 79,
                  80, 266, 275, 285, 289),
    ('r', 'cd'): (13, 14, 15, 16, 35, 36, 37, 44, 138, 147),
    ('t', 'bc'): (41, 42, 61, 62, 86, 138),
    ('t', 'bd'): (28, 29, 42, 43, 63, 64, 68, 69, 75, 76, 80, 81, 92, 100,
                  153, 157),
    ('t', 'be'): (74, 75, 81, 82, 94, 114),
}

JOIN_SCORES = {
    -2: (13, 16),
    -1: (14, 35, 37, 44),
    1: (0, 3, 4, 5, 9, 17, 21, 23, 27, 28, 39, 46, 47, 49, 180),
    2: (1, 2, 18, 19, 22, 24, 38, 45),
    3: (20,),
}


def crossings(strands):
    return tuple(a + b for a, b in combinations(sorted(strands), 2))


def flipped(history, triangle):
    first, _, last = crossings(triangle)
    return history.index(first) < history.index(last)


def double_interval(family, stationary, early_pair, late_pair):
    early_mark = ''.join(sorted(early_pair + stationary))
    late_mark = ''.join(sorted(late_pair + stationary))
    # All crossings of g with x are early and those of f with x are late.
    # These comparisons also fix the order of both moving pairs at the cut.
    cut = (early_pair + stationary + late_pair[::-1] if family == 'r'
           else late_pair[::-1] + stationary + early_pair)
    early = {a+b for a, b in combinations(sorted(START), 2) if cut.index(a) < cut.index(b)}
    histories = raw_histories(START)
    boundaries = {h for h in histories if set(h[:len(early)]) == early}
    sources = {h for h in boundaries if not flipped(h, early_mark) and not flipped(h, late_mark)}
    targets = {h for h in boundaries if flipped(h, early_mark) and flipped(h, late_mark)}
    assert sources and targets
    allowed = {h for h in histories if flipped(h, late_mark) or not flipped(h, early_mark)}

    def monochromatic(e):
        return e.family == 'K15' or all(len(early.intersection(crossings(t))) in (0, 3)
                                         for t in gray(e))

    classes, at = restrict_interval(START, sources, targets, allowed, monochromatic)
    return classes, at, boundaries, len(early), early_mark, late_mark


def check_double(family, stationary, early_pair, late_pair):
    classes, at, boundaries, cut, early, late = double_interval(
        family, stationary, early_pair, late_pair)
    graph, labels = ground_interval(classes, at, loose=True)
    candidates = set()
    for e, name in labels.items():
        if e.family != family or not {early, late} <= set(gray(e)):
            continue
        readout = e.right_events if family == 'r' else e.left_events[::-1]
        if readout.index(late_pair) < readout.index(early_pair):
            candidates.add(int(name))
    support = set(DOUBLE_SCORES.get((family, early_pair), ()))
    assert bool(candidates) == bool(support)
    assert candidates <= support <= {int(e) for e in graph.edges}
    for e, name in labels.items():
        if e.source in boundaries and (e.hi <= cut or e.lo >= cut):
            assert int(name) not in support

    def value(path):
        return sum(int(e) in support for e in path.edges)

    for rule in graph.rules.values():
        before, after = value(rule.source), value(rule.target)
        assert before == after if rule.equation else before <= after
    return len(candidates), len(graph.edges), len(graph.rules)


def check_join():
    graph, _ = ground(loose=True)
    weights = {edge: score for score, edges in JOIN_SCORES.items() for edge in edges}
    rank = Rank({}, {e: int(e) for e in graph.edges}, weights)
    pairs = [(r.source, r.target) for r in graph.rules.values() if r.name.startswith('H_R ')]
    assert len(pairs) == 2 and verify_rank(graph, pairs, rank)
    assert all(rank.evaluate(p)[1] - rank.evaluate(q)[1] == 2 for p, q in pairs)


def check():
    check_join()
    results = []
    for family, stationary, moving in (('r', 'e', 'abcd'), ('t', 'a', 'bcde')):
        for pair in combinations(moving, 2):
            early = ''.join(pair)
            late = ''.join(v for v in moving if v not in early)
            results.append(check_double(family, stationary, early, late))
    assert len(results) == 12 and sum(bool(count) for count, _, _ in results) == 6
    print(f'Both projected H_R rules have drop 2. Of {len(results)} double-mark cuts, '
          f'6 have candidates; all {sum(n for n, _, _ in results)} projected edges score 1. '
          f'Checked {sum(n for _, _, n in results)} grounded comparisons.')


if __name__ == '__main__':
    check()
