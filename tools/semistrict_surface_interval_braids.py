"""Read the ordinary braid on each wire of a stationary interval history."""

from argparse import ArgumentParser
from itertools import combinations

from relative_coherence_strip_fibres import Complex, events
from semistrict_surface_shared_edge import braid_image


def observe(order, moves, intervals):
    order = list(order)
    lanes = range(max(b for _, b in intervals))
    words = [[] for _ in lanes]
    for position, sign in moves:
        if not 0 <= position < len(order) - 1:
            raise ValueError('exchange position outside the serial word')
        a, b = order[position:position+2]
        left = max(intervals[a][0], intervals[b][0])
        right = min(intervals[a][1], intervals[b][1])
        if sign not in ((-1, 1) if left < right else (0,)):
            raise ValueError('overlapping intervals require a signed switch; disjoint intervals require 0')
        for lane in range(left, right):
            before = sum(intervals[i][0] <= lane < intervals[i][1] for i in order[:position])
            words[lane].append(sign * (1 + before))
        order[position:position+2] = b, a
    actions = tuple(braid_image(sum(a <= lane < b for a, b in intervals), word)
                    for lane, word in zip(lanes, words))
    return tuple(order), actions


def audit(intervals):
    count = max(b for _, b in intervals)
    names = 'ABCDE'[:len(intervals)]
    rules = {n: {j: ('', '') for j in range(a, b)} for n, (a, b) in zip(names, intervals)}
    obj = Complex(('',) * count, ('',) * count, rules)
    assert len(obj.components) == 1
    vertices = {i: tuple(names.index(next(iter(events(t)))) for t in cell)
                for i, cell in enumerate(obj.cells) if obj.degrees[i] == 0}
    arcs = {}
    for i, cell in enumerate(obj.cells):
        if obj.degrees[i] != 1:
            continue
        pos = next(j for j, t in enumerate(cell) if len(events(t)) == 2)
        ends = obj.facets[i]
        arcs[i] = {}
        for start, end in (ends, ends[::-1]):
            a, b = vertices[start][pos:pos+2]
            common = [row for row in cell[pos] if len(row) == 2]
            assert len(set(common)) <= 1
            sign = 0 if not common else (1 if common[0] == names[a] + names[b] else -1)
            assert observe(vertices[start], [(pos, sign)], intervals)[0] == vertices[end]
            arcs[i][start] = end, (pos, sign)
    face_count = 0
    for dimension, boundary in zip(obj.degrees, obj.facets):
        if dimension != 2:
            continue
        start = next(iter(arcs[boundary[0]]))
        at, todo, moves = start, set(boundary), []
        while todo:
            e = next(edge for edge in todo if at in arcs[edge])
            todo.remove(e)
            at, move = arcs[e][at]
            moves.append(move)
        assert at == start
        assert observe(vertices[start], moves, intervals) == observe(vertices[start], [], intervals)
        face_count += 1
    # Independently compare the computed cellular homology with the
    # successive punctured-plane fibre ranks of interval elimination.
    remaining = set(range(len(intervals)))
    polynomial = [1]
    while remaining:
        v = min(remaining, key=lambda i: intervals[i][1])
        remaining.remove(v)
        wire = intervals[v][1] - 1
        k = sum(intervals[i][0] <= wire < intervals[i][1] for i in remaining)
        polynomial = [a+b for a, b in zip(polynomial + [0], [0] + [x*k for x in polynomial])]
    while polynomial[-1] == 0:
        polynomial.pop()
    assert obj.betti(obj.components[0]) == tuple(polynomial)
    return len(vertices), len(arcs), face_count, tuple(polynomial)


def parse_pairs(values):
    result = []
    for value in values:
        fields = value.split(',')
        if len(fields) != 2:
            raise ValueError('expected a pair I,J')
        result.append(tuple(map(int, fields)))
    return result


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--intervals', nargs='+', metavar='A,B', help='nonempty half-open intervals of wire indices')
    parser.add_argument('--moves', nargs='*', metavar='I,S', default=[], help='zero-based adjacent position and chart sign')
    args = parser.parse_args()
    if args.intervals:
        try:
            slots = parse_pairs(args.intervals)
            if any(not 0 <= a < b for a, b in slots):
                raise ValueError('each interval must satisfy 0 <= A < B')
            end, actions = observe(range(len(slots)), parse_pairs(args.moves), slots)
        except ValueError as e:
            parser.error(str(e))
        print('labelled serial endpoint:', end)
        print('Artin actions by wire:', actions)
    else:
        if args.moves:
            parser.error('--moves requires --intervals')
        for slots in ([(0, 2), (1, 3), (2, 4)], [(0, 2), (1, 3), (2, 4), (1, 2)],
                      [(0, 3), (1, 2), (1, 2), (3, 4)]):
            print(slots, 'vertices, edges, two-cells, Betti numbers:', audit(slots))
        slots = [(0, 3), (1, 2), (1, 2)]
        order = tuple(range(3))
        commutator = (1, 1, 2, 2, -1, -1, -2, -2)
        moves = [(abs(s)-1, 1 if s > 0 else -1) for s in commutator]
        end, actions = observe(order, moves, slots)
        assert end == order and actions[1] != observe(order, [], slots)[1][1]
        # Deleting any strand makes the two pure generators commute.
        for pair in combinations(order, 2):
            kept = [i for i in order if i in pair]
            current = list(order)
            word = []
            for i, sign in moves:
                p, q = current[i:i+2]
                if p in kept and q in kept:
                    word.append(sign)
                current[i:i+2] = q, p
            assert braid_image(2, word) == braid_image(2, ())
        print('nonidentity three-strand commutator with identity on every pair')
