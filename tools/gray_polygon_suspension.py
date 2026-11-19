"""Check the diagonal section for a polygon tensored with a suspension."""
import argparse
import json
from collections import Counter
from functools import cache
from itertools import product

from gray_globe_comparison import atom, close_atoms, face
from gray_tree_section import generators, section, tree_boundary


ENDPOINTS = [(0, (2, side)) for side in (0, 1)]
TOP = (2, (2, 0))
INTERVAL = ((),)


class Polygon:
    def __init__(self, lengths, split):
        self.lengths = lengths
        self.split = split
        self.boundary = {}
        for b, length in enumerate(lengths):
            for i in range(length + 1):
                self.boundary[self.vertex(b, i)] = {}
            for i in range(length):
                self.boundary[1, (b, i)] = {self.vertex(b, i): -1, self.vertex(b, i + 1): 1}
        top = {(1, (b, i)): 2 * b - 1 for b, length in enumerate(lengths) for i in range(length)}
        if split:
            for side in (0, 1):
                index = [side * length for length in lengths]
                hidden = (1, (2, side))
                self.boundary[hidden] = {self.vertex(b, i): 2 * b - 1 for b, i in enumerate(index)}
                top[hidden] = 1 - 2 * side
        self.boundary[TOP] = top

    def vertex(self, branch, index):
        if not self.split:
            if index == 0:
                return ENDPOINTS[0]
            if index == self.lengths[branch]:
                return ENDPOINTS[1]
        return 0, (branch, index)

    def atoms(self, tree):
        def differential(basis):
            g, p = basis
            result = Counter({(y, p): n for y, n in self.boundary[g].items()})
            for (q,), n in tree_boundary((p,)).items():
                result[g, q] += (-1)**g[0] * n
            return result

        # atom reads the degree from the first field of each factor.
        def degree(rank):
            return rank if isinstance(rank, int) else len(rank)

        return {b: atom(b, differential, degree) for b in product(self.boundary, generators(tree))}


def verify(lengths, tree):
    if min(lengths) < 1:
        raise ValueError('both polygon sides must be nonempty')
    base = Polygon(lengths, False)
    split = Polygon(lengths, True)
    source = split.atoms(tree)
    target = base.atoms((tree,))
    corners = tuple(((v, ((), side)),) for side, v in enumerate(ENDPOINTS))

    def basis_image(g, p):
        d, (b, i) = g
        suspended = (0,) + p[0], p[1]
        is_hidden = d == 1 and b == 2
        collapsed = base.vertex(b, i) if d == 0 else g
        terms = [] if is_hidden else [(collapsed, suspended)]
        if not p[0]:
            if d == 0:
                terms.extend(((1, (b, j)), ((), int(j >= i))) for j in range(lengths[b]))
            if is_hidden:
                terms.append((TOP, ((), 1 - i)))
        return terms

    def image(x):
        def map_chain(chain):
            return tuple(sorted(term for g, p in chain for term in basis_image(g, p)))

        return (corners,) + tuple(tuple(map_chain(chain) for chain in pair) for pair in x)

    def local(g, side):
        d, (b, i) = g
        if d == 2:
            return (0, 0), 0
        if d == 0 and b == 2:
            return (), i
        selected = (lengths[b] - 1) * side
        if d == 0:
            return (), int(i > selected)
        if i == selected:
            return (0,), b
        return None

    @cache
    def lift(y):
        def unique_columns(chain):
            return [(g, (addr[1:], label)) for g, (addr, label) in chain
                    if addr and g not in ENDPOINTS]

        rows = [[unique_columns(chain) for chain in pair] for pair in y[1:]]
        for side in (0, 1):
            small = tuple(tuple(tuple(sorted((q, p) for g, p in chain
                                             if (q := local(g, side)) is not None))
                                for chain in pair) for pair in y)
            box = section(INTERVAL, tree, small)
            for row, pair in zip(rows, box, strict=True):
                for entries, chain in zip(row, pair):
                    for (address, branch), mid, p in chain:
                        if mid == ((), side):
                            g = (1, (2, side)) if address else split.vertex(branch, side * lengths[branch])
                            entries.append((g, p))
        return tuple(tuple(tuple(sorted(entries)) for entries in row) for row in rows)

    for degree in range(max(map(len, source.values())) + 1):
        candidates = close_atoms(source.values(), degree)
        diagonal = {y for y in close_atoms(target.values(), degree + 1) if y[0] == corners}
        for y in diagonal:
            x = lift(y)
            assert x in candidates and image(x) == y
            if degree:
                assert all(face(x, s) == lift(face(y, s)) for s in (0, 1))
                if y[-1] == ((), ()):
                    assert x[-1] == ((), ())
        print(f'Hom degree {degree}: {len(diagonal)} sections with prescribed faces')
    for p in generators(tree):
        x = source[TOP, p]
        y = target[TOP, ((0,) + p[0], p[1])]
        assert image(x) == y and lift(y) == x


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('negative', type=int)
    parser.add_argument('positive', type=int)
    parser.add_argument('tree', type=json.loads, help='tree before suspension')
    args = parser.parse_args()
    verify((args.negative, args.positive), args.tree)
