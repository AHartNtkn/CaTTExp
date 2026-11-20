"""Check typed-box intersections and relative past links for the guarded switch."""

from collections import Counter
from functools import cache
from itertools import combinations, product

from homotopy_polygraph_precedence import betti


def subsets(bits):
    part = bits
    while part:
        yield part
        part = (part - 1) & bits


def members(bits):
    while bits:
        bit = bits & -bits
        yield bit.bit_length() - 1
        bits ^= bit


class Board:
    def __init__(self, rows, cols, missing):
        self.rows = tuple(range(rows))
        self.cols = tuple(range(rows, rows + cols))
        self.s, self.t, self.z = range(rows + cols, rows + cols + 3)
        self.n = self.z + 1
        self.missing = tuple((a, rows + b) for a, b in missing)
        self.arcs = []

        def arrow(i, u, j, v):
            self.arcs.append((i, u, j, v))

        def incompatible(i, u, j, v):
            arrow(i, u, j, v)
            arrow(j, v, i, u)

        def cycle(nodes):
            for (i, u), (j, v) in zip(nodes, nodes[1:] + nodes[:1]):
                arrow(i, u, j, v)

        cycle([(self.s, 2)] + [(a, 1) for a in self.rows])
        cycle([(self.t, 1)] + [(b, 2) for b in self.cols])
        for a in self.rows:
            incompatible(self.t, 2, a, 1)
            arrow(self.z, 3, a, 2)
        for b in self.cols:
            incompatible(self.s, 1, b, 2)
            arrow(b, 1, self.z, 3)
        incompatible(self.z, 3, self.s, 1)
        incompatible(self.z, 3, self.t, 2)
        for a, b in self.missing:
            arrow(a, 2, b, 1)

    def guard(self, roles):
        pre = lambda i: roles[i] & 1
        post = lambda i: roles[i] & 2
        switch = roles[self.z] == 3
        return not (
            post(self.s) and all(pre(a) for a in self.rows)
            or pre(self.t) and all(post(b) for b in self.cols)
            or pre(self.s) and any(post(b) for b in self.cols)
            or post(self.t) and any(pre(a) for a in self.rows)
            or switch and (pre(self.s) or post(self.t)
                           or any(post(a) and pre(b) for a, b in self.missing))
        )


def compile_boxes(board):
    """Generate the projected boxes, exceptional heights and private clock sites."""
    role_span = {1: (0, 1), 2: (1, 2), 3: (0, 3)}
    kinds = [0] * len(board.rows) + [1] * len(board.cols) + [2, 3, 4]
    boxes = {}
    for i, kind in enumerate(kinds):
        x = (0, 2 * len(board.cols) + 1)
        y = (0, 2 * len(board.rows) + 1)
        if kind == 0:
            y = (2 * i + 1, 2 * i + 3)
        if kind == 1:
            j = i - len(board.rows)
            x = (2 * j + 1, 2 * j + 3)
        for role in role_span:
            tags = [(0, 4)] * 5
            tags[kind] = role_span[role]
            boxes[i, role] = [(2 * x[0], 2 * x[1] + 1), y, *tags]

    def inside(point, key):
        return all(lo <= x <= hi for x, (lo, hi) in zip(point, boxes[key]))

    def position(indices):
        if len(indices) == 2:
            assert max(indices) == min(indices) + 1
            return 2 * min(indices) + 3
        return 2 * indices[0] + 2 if indices else 0

    def base_point(actors, tag_values, bit):
        x = position([i - len(board.rows) for i in actors if kinds[i] == 1])
        y = position([i for i in actors if kinds[i] == 0])
        tags = [4] * 5
        for i, value in zip(actors, tag_values):
            assert tags[kinds[i]] in (4, value)
            tags[kinds[i]] = value
        u = (2 * x + bit, y, *tags)
        assert {i for i in range(board.n) if inside(u, (i, 3))} == set(actors)
        return u

    for i in range(board.n):
        p = base_point([i], [1], 0)
        assert inside(p, (i, 1)) and inside(p, (i, 2))

    heights, clock_sites = {}, {}
    tag = {1: 0, 2: 2, 3: 3}
    for i, s, j, t in board.arcs:
        u = base_point([i, j], [tag[s], tag[t]], int(i > j))
        heights[u, max(i, j)] = min(i, j)
        assert inside(u, (i, s)) and inside(u, (j, t))
        assert u not in clock_sites or clock_sites[u] == (i, j)
        clock_sites[u] = i, j

    table = {}
    for i, j in combinations(range(board.n), 2):
        for r, s in product(role_span, repeat=2):
            orders = set()
            for u, order in clock_sites.items():
                if inside(u, (i, r)) and inside(u, (j, s)):
                    hi, hj = heights.get((u, i), i), heights.get((u, j), j)
                    assert hi <= hj
                    if hi == hj:
                        assert set(order) == {i, j}
                        orders.add(order)
            expected = {(a, b) for a, p, b, q in board.arcs
                        if a == i and b == j and p & r == p and q & s == q
                        or a == j and b == i and p & s == p and q & r == q}
            assert orders == expected
            table[i, r, j, s] = tuple(orders)
    return table, len(boxes[0, 3]) + 1


def acyclic_chart(n, pair_orders):
    incoming = [0] * n
    after = [[] for _ in range(n)]
    for orders in pair_orders:
        for i, j in orders:
            incoming[j] += 1
            after[i].append(j)
    ready = [i for i in range(n) if incoming[i] == 0]
    count = 0
    while ready:
        i = ready.pop()
        count += 1
        for j in after[i]:
            incoming[j] -= 1
            if not incoming[j]:
                ready.append(j)
    return count == n


@cache
def link_type(face_list):
    """A point certificate by elementary simplicial collapses, or actual Betti numbers."""
    faces = set(face_list)
    while len(faces) > 1:
        upper = {f: [] for f in faces}
        for f in faces:
            for i in members(f):
                if f != 1 << i:
                    upper[f ^ (1 << i)].append(f)
        pair = next(((f, ups[0]) for f, ups in upper.items()
                     if len(ups) == 1 and not upper[ups[0]]), None)
        if pair is None:
            return betti(faces), False
        faces.difference_update(pair)
    return (1,), True


def audit(board, *, expected_full=(1,)):
    table, dimension = compile_boxes(board)
    all_actors = (1 << board.n) - 1
    pairs = tuple(combinations(range(board.n), 2))
    counts = Counter()
    for present in range(all_actors + 1):
        cube = set()
        valid = set()
        for end in [0, *subsets(present)]:
            for moving in [0, *subsets(end)]:
                roles = tuple(0 if not present & (1 << i) else 3 if moving & (1 << i)
                              else 2 if end & (1 << i) else 1 for i in range(board.n))
                orders = (table[i, roles[i], j, roles[j]] for i, j in pairs if roles[i] and roles[j])
                legal = acyclic_chart(board.n, orders)
                assert legal == board.guard(roles)
                counts['cubes tested'] += 1
                if legal:
                    cube.add((end, moving))
                    if not moving:
                        valid.add(end)
        for start in valid:
            reachable = {start}
            for end in sorted(valid):
                if end == start or start & ~end:
                    continue
                faces = tuple(sorted(m for m in subsets(end ^ start)
                                     if (end, m) in cube and end ^ m in reachable))
                if not faces:
                    continue
                reachable.add(end)
                counts['intervals'] += 1
                homology, collapsed = link_type(faces)
                if not collapsed:
                    assert present == all_actors and start == 0 and end == all_actors, (
                        present, start, end, homology, faces)
                    assert homology == expected_full, (homology, expected_full)
                    counts['noncollapsing full link'] += 1
                else:
                    counts['collapsed'] += 1
    print(f'Spatial dimension {dimension}; {dict(counts)}.', flush=True)
    assert counts['noncollapsing full link'] == int(expected_full != (1,))


if __name__ == '__main__':
    diagonal = [(0, 0), (1, 1), (2, 2)]
    audit(Board(1, 1, []))
    audit(Board(2, 2, [(0, 1), (1, 0)]), expected_full=(2,))
    audit(Board(3, 3, diagonal), expected_full=(1, 1))
    audit(Board(4, 3, diagonal))
