"""Check binary exchange links and ternary attaching loops in actual chart fibres."""

from collections import defaultdict
from itertools import combinations, permutations

from homotopy_polygraph_counter_ring import counter_ring
from relative_coherence_spherical_fibres import ring
from relative_coherence_strip_fibres import Complex, events


def swap_labels(history):
    labels = []
    start = 0
    for chart in history:
        size = len(events(chart))
        if size == 2:
            labels.append((start, chart))
        start += size
    return tuple(labels)


def serial_order(history):
    return tuple(next(iter(events(chart))) for chart in history)


def hexagon_order(model, face):
    neighbors = defaultdict(list)
    for edge in model.facets[face]:
        a, b = model.facets[edge]
        neighbors[a].append(b)
        neighbors[b].append(a)
    assert len(neighbors) == 6 and all(len(n) == 2 for n in neighbors.values())
    cycle = [next(iter(neighbors))]
    previous = None
    while True:
        after = next(v for v in neighbors[cycle[-1]] if v != previous)
        if after == cycle[0]:
            assert len(cycle) == 6
            return [serial_order(model.cells[v]) for v in cycle]
        assert after not in cycle
        previous = cycle[-1]
        cycle.append(after)


def check_model(name, model):
    vertices = {i for i, dim in enumerate(model.degrees) if dim == 0}
    binary = {i for i, cell in enumerate(model.cells) if all(len(events(t)) <= 2 for t in cell)}
    links = {v: set() for v in vertices}
    for i in binary:
        labels = swap_labels(model.cells[i])
        for v in vertices.intersection(model.ideal(i)):
            order = serial_order(model.cells[v])
            corner = frozenset((p, chart, order[p] < order[p + 1]) for p, chart in labels)
            assert corner not in links[v]
            links[v].add(corner)
    for faces in links.values():
        germs = [next(iter(face)) for face in faces if len(face) == 1]
        # Extend each simplex by each commuting germ. Induction checks every clique.
        for face in faces:
            for germ in germs:
                if all(abs(germ[0] - other[0]) > 1 for other in face):
                    assert face | {germ} in faces

    names = serial_order(model.cells[min(vertices)])
    hexagons = 0
    for i, dim in enumerate(model.degrees):
        large = [events(t) for t in model.cells[i] if len(events(t)) == 3]
        if dim != 2 or not large:
            continue
        cycle = hexagon_order(model, i)
        for a, b, c in combinations(names, 3):
            target = [(a, b, c), (b, a, c), (b, c, a), (c, b, a), (c, a, b), (a, c, b)]
            positions = [target.index(tuple(x for x in perm if x in (a,b,c))) for perm in cycle]
            increments = [(v - u) % 6 for u, v in zip(positions, positions[1:] + positions[:1])]
            assert set(increments) <= {0, 1, 5}
            winding = increments.count(1) - increments.count(5)
            assert abs(winding) == (6 if large[0] == {a, b, c} else 0)
        hexagons += 1
    component, = model.components
    result = (len(vertices), len(binary), hexagons, model.betti(binary), model.betti(component))
    print(name, result)
    return result


def check_insertions(n):
    """Time beads in the suspension of the planar generator from the empty word to t."""
    orders = set()
    for word in permutations(range(n)):
        for flags in range(1 << (n - 1)):
            blocks = []
            first = 0
            for i in range(n):
                if i == n - 1 or flags & (1 << i):
                    blocks.append(frozenset(word[first:i + 1]))
                    first = i + 1
            orders.add(tuple(blocks))

    moves = {v: {} for v in orders}
    edges = {}

    def add_move(source, label, target, edge):
        assert label not in moves[source]
        moves[source][label] = (target, edge)

    for fine in orders:
        past = set()
        for i, (a, b) in enumerate(zip(fine, fine[1:])):
            coarse = fine[:i] + (a | b,) + fine[i + 2:]
            # Literal spatial word of old gates and two colours of the insertion.
            chart = ''.join('t' if j in past else '1' if j in a else '2'
                            for j in range(n) if j in past | a | b)
            tag = (len(past), len(past | a | b), chart)
            edge = len(edges)
            edges[fine, coarse] = edge
            add_move(coarse, (*tag, 1), fine, edge)
            add_move(fine, (*tag, -1), coarse, edge)
            past.update(a)

    def boundary(edge_list):
        return sum(1 << e for e in edge_list)

    disjoint = set()
    ternary = set()
    for v, germs in moves.items():
        for (g, (vg, eg)), (h, (vh, eh)) in combinations(germs.items(), 2):
            if g[1] <= h[0] or h[1] <= g[0]:
                end, egh = moves[vg][h]
                other, ehg = moves[vh][g]
                assert end == other
                disjoint.add(boundary((eg, eh, egh, ehg)))
        for i in range(len(v) - 2):
            a, b, c = v[i:i + 3]
            left = v[:i] + (a | b, c) + v[i + 3:]
            right = v[:i] + (a, b | c) + v[i + 3:]
            base = v[:i] + (a | b | c,) + v[i + 3:]
            ternary.add(boundary((edges[v, left], edges[left, base],
                                  edges[v, right], edges[right, base])))
    assert disjoint.isdisjoint(ternary)

    def first_betti(columns):
        basis = {}
        for col in columns:
            while col and col.bit_length() in basis:
                col ^= basis[col.bit_length()]
            if col:
                basis[col.bit_length()] = col
        # Every ordered partition can merge to the same one-block vertex.
        return len(edges) - len(orders) + 1 - len(basis)

    result = (len(orders), len(edges), len(disjoint), len(ternary),
              first_betti(disjoint), first_betti(disjoint | ternary))
    print(f'{n} suspended insertions', result)
    return result


if __name__ == '__main__':
    assert check_insertions(3) == (13, 18, 0, 6, 6, 0)
    assert check_insertions(4) == (75, 158, 24, 84, 60, 0)
    for n, expected in [(3, (6, 12, 1, (1, 1), (1,))),
                        (4, (24, 66, 8, (1, 7), (1,)))]:
        model = Complex(('a',) * n, ('b',) * n,
                        {chr(65 + i): {i: ('a', 'b')} for i in range(n)})
        assert check_model(f'{n} independent events', model) == expected

    # Two distinct exchange edges with the same endpoints on a common idle wire.
    model = Complex(('a', '', 'p'), ('b', '', 'q'),
                    {'A': {0: ('a', 'b'), 1: ('', '')}, 'B': {1: ('', ''), 2: ('p', 'q')}})
    assert check_model('middle wire', model) == (2, 4, 0, (1, 1), (1, 1))
    model = Complex(*ring(2))
    result = check_model('two-seam ring', model)
    assert result[1:] == (96, 0, (1, 1), (1, 1))
    result = check_model('counter ring', Complex(*counter_ring()))
    assert result[1:] == (512, 0, (1, 1), (1, 1))
