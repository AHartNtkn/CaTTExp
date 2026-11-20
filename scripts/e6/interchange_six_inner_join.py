"""A right inner exchange opposite a left crossing on six distinct factors.

Two adjacent descending pairs in the right quartet advance before the cut.
The late half moves the left pair ab through the quartet and sorts ab.
The outer 2-boundaries fix these eleven events for every representative.
The only monochromatic triangles are abx. Thus a proper six-strand
shifted join, requiring two disjoint triples, cannot occur on a return.
Test all six ordered matchings on cdef. Each has a proper H_R variation.
"""

from collections import Counter
from itertools import combinations

from interchange_five_cut_ranks import integer_rank, projected_deltas
from interchange_regular_rectangles import find_rank, verify_rank
from interchange_sorting_fiber import raw_histories, states
from interchange_six_shifted_join import respects_incidences
from interchange_triangle_join_interval import gray, ground_interval, restrict_interval


def check_cut(left_pair, right_pair):
    start = left_pair[::-1] + right_pair[::-1] + 'ba'
    cut = left_pair + right_pair + 'ba'
    end = 'ab' + left_pair + right_pair
    histories = set(raw_histories(start, end))
    seeds = {h for h in histories if cut in states(start, h)}
    early = {left_pair, right_pair}
    late = {'ab'} | {x + y for x in 'ab' for y in 'cdef'}
    assert all(set(h) == early | late for h in histories)
    triangles = {''.join(triple) for triple in combinations('abcdef', 3)
                 if {a + b for a, b in combinations(triple, 2)} <= late}
    assert triangles == {'ab' + x for x in 'cdef'}
    classes, at = restrict_interval(start, seeds, seeds, histories,
                                    lambda e: e.family == 'K15' or set(gray(e)) <= triangles)
    graph, labels = ground_interval(classes, at)
    pairs = [(a, d) for h in seeds for a in at[h] if a.hi <= 2
             for d in at[h] if d.lo >= 2]
    deltas = projected_deltas(pairs, 2, classes, at, labels)
    rules = Counter(r.name.split()[0] for r in graph.rules.values())
    joins = {(r.source, r.target) for r in graph.rules.values() if r.name.startswith('H_R ')}
    temporal = {(r.source, r.target) for r in graph.rules.values() if r.name.startswith('delta ')}
    assert deltas and deltas <= temporal and joins and rules['factor']
    # Strictness on H_R also tests the step which moves an early variation
    # past the late join in the opposite order to the rectangle.
    strict = sorted(deltas | joins)
    rank = find_rank(graph, strict)
    assert rank is not None and verify_rank(graph, strict, integer_rank(rank))
    return len(histories), len(graph.edges), len(graph.rules), len(deltas), len(joins)


def check():
    for pair in combinations('cdef', 2):
        left = ''.join(pair)
        right = ''.join(x for x in 'cdef' if x not in left)
        counts = check_cut(left, right)
        assert counts == (2145, 514, 1193, 144, 1)
        print(f'{left}|{right}: histories, edges, comparisons, strict cut swaps, strict H_R = {counts}')
    check_flag()


def check_flag():
    """Replay the crossing-order score on a full six-strand interval."""
    start = 'fedcba'
    quartet = 'cdef'
    early = {a+b for a, b in combinations(quartet, 2)}
    late_marks = {'ab'+x for x in quartet}

    def flipped(p, triple):
        return p.index(triple[:2]) < p.index(triple[1:])

    frozen = tuple(''.join(t) for t in combinations(quartet, 3))
    histories = {p for p in raw_histories(start) if respects_incidences(p, early)
                 and not any(flipped(p, t) for t in frozen)}
    seeds = {p for p in histories if set(p[:6]) == early}
    sources = {p for p in seeds if not any(flipped(p, t) for t in late_marks)}
    targets = {p for p in seeds if all(flipped(p, t) for t in late_marks)}
    classes, at = restrict_interval(start, sources, targets, histories,
                                    lambda e: e.family == 'K15' or set(gray(e)) <= late_marks)
    graph, labels = ground_interval(classes, at)
    flag, packets, products = {}, {}, {}
    for e, n in labels.items():
        left, right = early.intersection(e.left_events), early.intersection(e.right_events)
        value = 0
        if e.family == 'i' and left and right:
            left_event, = left
            right_event, = right
            assert set(left_event + right_event) == set(quartet)
            value = int(e.source.index('ab') < e.source.index(right_event))
        assert flag.setdefault(n, value) == value
        assert packets.setdefault(n, frozenset(gray(e))) == set(gray(e))
        if e.family == 'i':
            operands = (frozenset(e.left_events), frozenset(e.right_events))
            assert products.setdefault(n, operands) == operands

    drops = strict_joins = 0
    for rule in graph.rules.values():
        change = sum(flag[n] for n in rule.target.edges) - sum(flag[n] for n in rule.source.edges)
        if rule.equation:
            assert change == 0
        elif change < 0:
            # Project the right-hand variation to its triangle and the
            # independent left operand to one early event. The resulting
            # proper N_R is strictly separated by the five-strand checker.
            assert rule.name.startswith('N_R ')
            varied, product = rule.source.edges
            left, right = products[product]
            assert left & early and any(
                {a+b for a, b in combinations(t, 2)} <= right for t in packets[varied] & late_marks)
            drops += 1
        if rule.name.startswith('H_R '):
            assert change == 1
            strict_joins += 1
    assert (len(classes), len(graph.edges), len(graph.rules), strict_joins, drops) == (
        2288, 10804, 46446, 3, 3)
    print(f'Full interval: {len(graph.rules)} comparisons. All {strict_joins} right join '
          f'variations raise the flag; all {drops} decreases project to forbidden naturalities.')


if __name__ == '__main__':
    check()
