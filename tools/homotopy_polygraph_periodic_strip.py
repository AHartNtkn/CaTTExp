"""Check the constant-width routing of the guarded switch on a chain of blocks."""

from collections import Counter, defaultdict
from graphlib import TopologicalSorter
from itertools import product

from homotopy_polygraph_guarded_boxes import Board


def strip_arcs(rows, columns, incident):
    """Ports are (slab, local name, literal). Literal zero denotes a passive node."""
    count = len(rows)
    edges = set()
    s, t, z = ((0, name) for name in ('S', 'T', 'Z'))

    def port(node, literal):
        return (*node, literal)

    def connect(source, target):
        assert abs(source[0] - target[0]) <= 1
        edges.add((source, target))

    def spine(name, direction):
        nodes = [(i, name, 0) for i in range(count)]
        order = nodes if direction == 1 else nodes[::-1]
        for source, target in zip(order, order[1:]):
            connect(source, target)
        return nodes

    def broadcast(name, master, recipients, outward):
        nodes = spine(name, 1 if outward else -1)
        if outward:
            connect(master, nodes[0])
            for endpoint in recipients:
                connect(nodes[endpoint[0]], endpoint)
        else:
            connect(nodes[0], master)
            for endpoint in recipients:
                connect(endpoint, nodes[endpoint[0]])

    all_rows = [a for slab in rows for a in slab]
    all_cols = [b for slab in columns for b in slab]
    for master, actors, literal, name in [
        (port(s, 2), all_rows, 1, 'row-return'),
        (port(t, 1), all_cols, 2, 'column-return'),
    ]:
        chain = [master] + [port(actor, literal) for actor in actors]
        for a, b in zip(chain, chain[1:]):
            connect(a, b)
        back = spine(name, -1)
        connect(chain[-1], back[-1])
        connect(back[0], master)

    for master, actors, literal, name in [
        (port(s, 1), all_cols, 2, 'S-columns'),
        (port(t, 2), all_rows, 1, 'T-rows'),
    ]:
        endpoints = [port(a, literal) for a in actors]
        broadcast(name + '-out', master, endpoints, True)
        broadcast(name + '-in', master, endpoints, False)
        connect(master, port(z, 3))
        connect(port(z, 3), master)

    broadcast('Z-rows', port(z, 3), [port(a, 2) for a in all_rows], True)
    broadcast('columns-Z', port(z, 3), [port(b, 1) for b in all_cols], False)

    for direction in (1, -1):
        nodes = spine('far' + str(direction), direction)
        for i in range(count):
            j = i + direction
            if 0 <= j < count:
                for row in rows[i]:
                    connect(port(row, 2), nodes[j])
                for column in columns[j]:
                    connect(nodes[i], port(column, 1))
    for row in all_rows:
        for j in range(max(0, row[0] - 1), min(count, row[0] + 2)):
            for column in columns[j]:
                if (row, column) not in incident:
                    connect(port(row, 2), port(column, 1))
    return edges


def audit(row_counts, col_counts, incidences):
    rows = [[(i, f'a{k}') for k in range(m)] for i, m in enumerate(row_counts)]
    cols = [[(i, f'b{k}') for k in range(m)] for i, m in enumerate(col_counts)]
    a_list, b_list = sum(rows, []), sum(cols, [])
    actors = a_list + b_list + [(0, x) for x in ('S', 'T', 'Z')]
    missing = [(i, j) for i, a in enumerate(a_list) for j, b in enumerate(b_list)
               if (a, b) not in incidences]
    board = Board(len(a_list), len(b_list), missing)
    expected = {((*actors[i], u), (*actors[j], v)) for i, u, j, v in board.arcs}

    edges = strip_arcs(rows, cols, incidences)
    after = defaultdict(set)
    passive = TopologicalSorter()
    for source, target in edges:
        after[source].add(target)
        if not source[2] and not target[2]:
            passive.add(target, source)
    tuple(passive.static_order())
    recovered = set()
    for start in [p for p in after if p[2]]:
        todo = list(after[start])
        seen = set()
        while todo:
            p = todo.pop()
            if p in seen:
                continue
            seen.add(p)
            if p[2]:
                recovered.add((start, p))
            else:
                todo.extend(after[p])
    assert recovered == expected

    # The transfer lane uses the local port pair, relative displacement and
    # the residue of the source slab. Its translates must have disjoint spans.
    lanes = defaultdict(list)
    for a, b in edges:
        lane = (a[1:], b[1:], b[0] - a[0], a[0] % 3)
        lanes[lane].append(sorted((a[0], b[0])))
    for intervals in lanes.values():
        intervals.sort()
        assert all(left[1] < right[0] for left, right in zip(intervals, intervals[1:]))
    slab_load = Counter(min(a[0], b[0]) for a, b in edges)
    return len(lanes), max(slab_load.values())


if __name__ == '__main__':
    for mask in range(16):
        incident = {((a, 'a0'), (b, 'b0')) for a, b in product(range(2), repeat=2)
                    if mask & (1 << (2*a + b))}
        audit([1, 1], [1, 1], incident)
    print('All 16 two-slab incidence matrices recover the literal comparisons.')

    for length in (1, 2, 3, 4, 8, 16, 64):
        # One triangle per slab, glued to its neighbour at an endpoint.
        row_counts = [2] * (length - 1) + [3]
        incidences = {((i, f'a{k}'), (i, 'b0')) for i in range(length) for k in (0, 1)}
        incidences.update(((i + 1, 'a0'), (i, 'b0')) for i in range(length - 1))
        incidences.add(((length - 1, 'a2'), (length - 1, 'b0')))
        lanes, load = audit(row_counts, [1] * length, incidences)
        print(f'{length} triangles: {lanes} transfer lanes, at most {load} arcs per slab.')
