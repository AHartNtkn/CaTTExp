"""Conserved charges on the pure four-strand interval and its temporal cuts.

The certificate columns are indexed by the canonical ground_interval labels.
They count, respectively, the two orientations of the nonloop inner crossing
and all inner loops. A proper inner occurrence contributes one unit to exactly
one column. Number units along a path: even when the same loop repeats, a
chosen unit has a unique edge and within-edge index after every rewrite.
"""
from collections import Counter
from itertools import permutations

from interchange_sorting_fiber import moves, raw_histories, states
from interchange_triangle_join_interval import gray, ground_interval, restrict_interval


START = 'dcba'
HISTORIES = frozenset(raw_histories(START))
CHARGES = (
    '00001111101000000000000000000000111011110000000110000',
    '00000000000000000000110111100000000000000100000000000',
    '10111101010001111011101211101101111000111211010111011',
)


def check_charges():
    classes, at = restrict_interval(START, HISTORIES, HISTORIES, HISTORIES, lambda e: True)
    graph, labels = ground_interval(classes, at)
    assert all(len(column) == len(graph.edges) for column in CHARGES)
    for rule in graph.rules.values():
        for column in CHARGES:
            def count(path):
                return sum(int(column[int(edge)]) for edge in path.edges)
            assert count(rule.source) == count(rule.target), rule

    kinds = Counter()
    for edge, label in labels.items():
        if edge.family != 'i':
            continue
        loops = classes[edge.source] == classes[edge.target]
        left, = edge.left_events
        right, = edge.right_events
        separate = {left, right} == {'ab', 'cd'}
        assert loops == (not separate)
        charge = tuple(int(column[int(label)]) for column in CHARGES)
        assert charge == (separate and left == 'cd', separate and left == 'ab', loops)
        kinds[charge] += 1
    assert len(kinds) == 3
    print(f'Three quartet charges conserved across {len(graph.rules)} comparisons '
          f'on {len(graph.edges)} contextual edge labels.')
    return labels


def check_cuts(labels):
    positive_cuts = set()
    witness_checks = [Counter(), Counter()]
    for letters in permutations(START):
        cut = ''.join(letters)
        seeds = {raw for raw in HISTORIES if cut in states(START, raw)}
        # A positive elementary occurrence in each window may be presented
        # simultaneously by concatenating independent representatives.
        has_pair = False
        supports = [set(), set()]
        witnesses = [set(), set()]
        for raw in seeds:
            k = tuple(states(START, raw)).index(cut)
            edges = [e for e in moves(START, raw) if e.family != 'K15']
            windows = ([e for e in edges if e.hi <= k], [e for e in edges if e.lo >= k])
            has_pair |= all(windows)
            for side, window in enumerate(windows):
                for edge in window:
                    positive = {i for i, column in enumerate(CHARGES)
                                if int(column[int(labels[edge])])}
                    supports[side].update(positive)
                    if edge.family == 'i':
                        witnesses[side].update(positive)
        # The first early unit and last late unit lie inside the active
        # paths regardless of the lengths of the two inactive paths.
        assert witnesses[0].isdisjoint(supports[1])
        assert witnesses[1].isdisjoint(supports[0])
        for side, marks in enumerate(witnesses):
            if marks:
                witness_checks[side]['cuts'] += 1
                witness_checks[side]['charges'] += len(marks)
                if not supports[1 - side]:
                    witness_checks[side]['one_side'] += 1
        if not has_pair:
            continue

        early = frozenset((a + b) for i, a in enumerate(cut) for b in cut[i+1:] if a < b)
        def admissible(edge):
            if edge.family == 'K15':
                return True
            for a, b, c in gray(edge):
                colors = {e in early for e in (a+b, a+c, b+c)}
                if len(colors) > 1:
                    return False
            return True

        classes, at = restrict_interval(START, seeds, seeds, HISTORIES, admissible)
        graph, _ = ground_interval(classes, at)
        assert len(classes) == 4 and len(graph.edges) == 3
        rule, = graph.rules.values()
        assert not rule.equation and rule.name.startswith('delta ')
        s, t = rule.source.edges, rule.target.edges
        # Giving one unit to either source-only label proves strictness under
        # arbitrary path contexts, including both loops with arbitrary powers.
        source_only, = set(s) - set(t)
        assert s.count(source_only) == 1 and t.count(source_only) == 0
        positive_cuts.add(cut)
    assert positive_cuts == {'badc', 'bdac', 'cadb', 'cdab'}
    assert all(count == {'cuts': 12, 'charges': 15, 'one_side': 8} for count in witness_checks)
    print('All four quartet cuts admitting positive updates in both windows '
          'have a single strictly ranked temporal exchange.')
    print('Each temporal orientation has 15 cut/inner-charge choices on 12 cuts; '
          'every chosen charge vanishes throughout the opposite window.')


if __name__ == '__main__':
    check_cuts(check_charges())
