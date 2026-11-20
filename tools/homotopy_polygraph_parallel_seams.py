"""Compute the bridge section of actual positive three-dimensional seam presentations."""

from collections import Counter
from itertools import combinations
from string import ascii_uppercase

from homotopy_polygraph_chart_corners import frames
from relative_coherence_strip_fibres import Complex, events, substitute


def bridges(orientations):
    rules = {'U': {}, 'V': {}}
    initial, final, ports = [], [], []
    available_names = iter(k for k in ascii_uppercase if k not in rules)
    for source, target in orientations:
        a, b = next(available_names), next(available_names)
        rules[a], rules[b] = {}, {}
        for position, owner, short in [('start', source, a), ('seam', None, None), ('end', target, b)]:
            lane = len(initial)
            if position == 'seam':
                initial.append('tdh')
                final.append('teh')
                ports.append({'t': 'up', 'h': 'pv', 'd': 'pp', 'e': 'pp',
                              'U': 'uu', 'V': 'vv', a: 'pp', b: 'pp'})
                rules[a][lane] = ('d', '')
                rules[b][lane] = ('', 'e')
                for bridge in 'UV':
                    rules[bridge][lane] = ('', '')
            else:
                other = 'V' if owner == 'U' else 'U'
                initial.append('lh' if owner == 'U' else 'tl')
                final.append('rh' if owner == 'U' else 'tr')
                ports.append({'l': 'xy', 'm': 'xy', 'r': 'xy', 't': 'ux', 'h': 'yv',
                              owner: 'xy', short: 'xy', other: 'uu' if other == 'U' else 'vv'})
                first, second = (owner, short) if position == 'start' else (short, owner)
                rules[first][lane] = ('l', 'm')
                rules[second][lane] = ('m', 'r')
                rules[other][lane] = ('', '')

    ends = [(p[w[0]][0], p[w[-1]][1]) for p, w in zip(ports, initial)]

    def typed(lane, word):
        start, end = ends[lane]
        for letter in word:
            left, right = ports[lane][letter]
            if left != start:
                return False
            start = right
        return start == end

    return tuple(initial), tuple(final), rules, typed


def serial_side(start, rules, typed):
    """Reachability omitting U, with exchange connectivity checked at each state."""
    by_weight = {(frozenset(), start)}
    reached = set(by_weight)
    incoming = {}
    square_edges = {}
    while by_weight:
        next_weight = set()
        for used, state in by_weight:
            enabled = set()
            for k in rules.keys() - used - {'U'}:
                for unary in frames(state, (k,), rules, typed):
                    enabled.add(k)
                    v = (used | {k}, substitute(unary, rules, (), 1))
                    incoming.setdefault(v, set()).add((state, unary))
                    next_weight.add(v)
            for a, b in combinations(sorted(enabled), 2):
                for square in frames(state, (a, b), rules, typed):
                    v = (used | {a, b}, substitute(square, rules, (), 1))
                    ends = []
                    for first, last in ((a, b), (b, a)):
                        step = substitute(square, rules, {first}, 0)
                        ends.append((substitute(step, rules, (), 1),
                                     substitute(square, rules, {last}, 1)))
                    square_edges.setdefault(v, []).append(ends)
        for v in next_weight:
            # Every shorter state has one prefix class by induction. Join its
            # one-step extensions exactly at the two paths around each square.
            germs = incoming[v]
            connected = {next(iter(germs))}
            previous_size = 0
            while previous_size < len(connected):
                previous_size = len(connected)
                for left, right in square_edges.get(v, ()):
                    if left in connected or right in connected:
                        connected.update((left, right))
            assert connected == germs
        reached.update(next_weight)
        by_weight = next_weight
    return reached


def check(orientations, direct=False):
    start, end, rules, typed = bridges(orientations)
    reverse = {k: {i: (t, s) for i, (s, t) in ports.items()} for k, ports in rules.items()}
    prefixes = serial_side(start, rules, typed)
    suffixes = serial_side(end, reverse, typed)
    cells = {}
    for used, state in prefixes:
        if not frames(state, ('U',), rules, typed):
            continue
        rest = [k for k in rules.keys() - used - {'U'} if frames(state, (k,), rules, typed)]
        for size in range(len(rest) + 1):
            for names in combinations(rest, size):
                for chart in frames(state, ('U',) + names, rules, typed):
                    after = substitute(chart, rules, (), 1)
                    if (frozenset(rules) - used - events(chart), after) in suffixes:
                        cells[used, state, chart] = len(cells)
    sizes, ranks, basis = Counter(), Counter(), {}
    for used, state, chart in cells:
        names = events(chart)
        degree = len(names) - 1
        sizes[degree] += 1
        column = 0
        for k in names - {'U'}:
            first_step = substitute(chart, rules, {k}, 0)
            new_state = substitute(first_step, rules, (), 1)
            column ^= 1 << cells[used | {k}, new_state, substitute(chart, rules, names - {k}, 1)]
            column ^= 1 << cells[used, state, substitute(chart, rules, names - {k}, 0)]
        while column:
            pivot = column.bit_length()
            if pivot not in basis:
                basis[pivot] = column
                ranks[degree] += 1
                break
            column ^= basis[pivot]
    betti = [sizes[k] - ranks[k] - ranks[k + 1] for k in range(max(sizes) + 1)]
    while betti and not betti[-1]:
        betti.pop()
    f = orientations.count('UV')
    cycles = (2**f - 1) * (2**(len(orientations) - f) - 1)
    assert betti == ([1, cycles] if cycles else [1])
    if direct:
        whole = Complex(start, end, rules, lambda tier: all(typed(i, w) for i, w in enumerate(tier)))
        label, = whole.components
        assert whole.betti(label) == tuple(betti)
        print(f'{len(label)} full histories checked independently.')
    print(f'{orientations}: {len(cells)} bridge-section cells, Betti {betti}.')


def check_persistent_gate():
    start, end, rules, typed = bridges(['UV', 'VU'])
    start = start[:1] + ('tddh',) + start[2:]
    end = end[:1] + ('tedh',) + end[2:]
    histories = Complex(start, end, rules, lambda tier: all(typed(i, w) for i, w in enumerate(tier)))
    counts = sorted((len(label), histories.betti(label)) for label in histories.components)
    assert counts == [(125, (1,)), (248, (1, 1))]
    print(f'Repeated gate: two strict fibres at the same endpoints, {counts}.')


if __name__ == '__main__':
    check_persistent_gate()
    check(['UV', 'VU'], direct=True)
    check(['UV', 'UV', 'VU'])
    check(['UV', 'UV', 'UV'])
    check(['UV', 'UV', 'VU', 'VU'])
