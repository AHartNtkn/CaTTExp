"""A globular section for two suspended globes, assembled from unit cubes."""
import argparse
from collections import Counter, defaultdict
from functools import cache
from itertools import product

from gray_globe_comparison import (CORNERS, atom, boundary, face, globe, image,
                                   strict_cells)

EMPTY_ROW = ((), ())


def trim(rows):
    rows = list(rows)
    while rows and rows[-1] == EMPTY_ROW:
        rows.pop()
    return tuple(rows)


def row_map(cell, skip, transform):
    def on_chain(chain):
        return tuple(sorted(z for g in chain if (z := transform(g)) is not None))
    return trim((on_chain(s), on_chain(t)) for s, t in cell[skip:])


def omit(cell, axis, level):
    """Level 0 augments an axis; level 1 keeps its edge and shifts down."""
    return row_map(cell, level, lambda g: g[:axis] + g[axis + 1:] if g[axis][0] == level else None)


def reverse(factor):
    d, tag = factor
    return (d, 1 - tag) if d == 0 and tag != 2 else factor


def reverse_axes(cell, axes):
    return row_map(cell, 0, lambda g: tuple(reverse(t) if i in axes else t
                                            for i, t in enumerate(g)))


def signature(x):
    return omit(x, 2, 0), omit(x, 0, 0), omit(x, 1, 1)


def cells(shape):
    return {trim(x) for x in strict_cells(shape, sum(shape))} | {()}


@cache
def local_section(p, q):
    """Build and exhaustively verify the four finite lookup tables."""
    groups = defaultdict(list)
    source = cells((p, 1, q))
    for x in source:
        groups[signature(x)].append(x)
    allowed = {(u, v, w) for u, v, w in product(cells((p, 1)), cells((1, q)),
                                                [reverse_axes(x, (1,)) for x in cells((p, q))])
               if omit(u, 0, 0) == omit(v, 1, 0) and omit(u, 1, 1) == omit(w, 1, 0)
               and omit(v, 0, 1) == omit(w, 0, 0)}
    assert groups.keys() == allowed

    pins = {}
    for l, r in product(globe(p), globe(q)):
        pending = [atom((l, (1, 2), r))]
        while pending:
            x = pending.pop()
            key = signature(x)
            if key in pins:
                assert pins[key] == x
                continue
            pins[key] = x
            if len(x) > 1:
                pending.extend(face(x, d) for d in (0, 1))

    def size(key):
        u, v, w = key
        return max(len(u), len(v), len(w) + 1 if w else 0)

    chosen = {}
    for key in sorted(groups, key=size):
        candidates = []
        for x in groups[key]:
            if len(x) != size(key) or (key in pins and pins[key] != x):
                continue
            if len(x) > 1 and any(chosen[signature(z)] != z
                                   for z in (trim(face(x, d)) for d in (0, 1))):
                continue
            candidates.append(x)
        assert candidates, key
        chosen[key] = min(candidates)
    return chosen


def window(factor, start):
    d, tag = factor
    return (0, tag) if d == start else (1, 2)


def outer_margin(y, first, h):
    """Project the diagonal to P⊗I or I⊗Q and take its rank-h window."""
    def basis(g):
        p, q = g
        outer, other = (p, q) if first else (q, p)
        if outer[0] not in (h + 1, h + 2) or other[0] > 1:
            return None
        f = window((outer[0] - 1, outer[1]), h)
        mid = (1, 2) if other[0] else (0, 1 - other[1] if first else other[1])
        if first and h % 2:
            mid = reverse(mid)
        return (f, mid) if first else (mid, f)
    return row_map(y, 1 + h, basis)


def crossing(y, i, j):
    def basis(g):
        p, q = g
        if p[0] not in (i + 1, i + 2) or q[0] not in (j + 1, j + 2):
            return None
        l = window((p[0] - 1, p[1]), i)
        r = window((q[0] - 1, q[1]), j)
        return l, reverse(r) if i % 2 else r
    return row_map(y, i + j + 2, basis)


def section(a, b, y):
    """Dimensions a,b are those of P,Q before suspension. Keep identity padding."""
    if y[0] != CORNERS or len(y) < 2:
        raise ValueError('expected a cell in the diagonal hom')
    panels = [[[], []] for _ in y[1:]]
    boxes = {}
    for i in range(min(a, len(panels) - 1) + 1):
        for j in range(min(b, len(panels) - 1 - i) + 1):
            u = omit(boxes[i, j - 1], 2, 1) if j else outer_margin(y, True, i)
            if i:
                v = reverse_axes(omit(boxes[i - 1, j], 0, 1), (0, 1))
            else:
                v = outer_margin(y, False, j)
            w = crossing(y, i, j)
            box = local_section(int(i < a), int(j < b))[u, v, w]
            boxes[i, j] = box
            if box:
                for d, chain in enumerate(box[0]):
                    (p, mid, q), = chain
                    if i % 2:
                        mid, q = reverse(mid), reverse(q)
                    panels[i + j][d].append(((i, p[1]), mid, (j, q[1])))

    def complete(chain, panel):
        mixed = [((p[0] - 1, p[1]), (1, 2), (q[0] - 1, q[1]))
                 for p, q in chain if p[0] and q[0]]
        return tuple(sorted(panel + mixed))
    return tuple(tuple(complete(chain, slots) for chain, slots in zip(row, panel))
                 for row, panel in zip(y[1:], panels))


def valid(x, bases):
    if len(x[0][0]) != 1 or len(x[0][1]) != 1 or x[-1][0] != x[-1][1]:
        return False
    for degree, row in enumerate(x):
        if any(g not in bases[degree] for chain in row for g in chain):
            return False
    for prev, row in zip(x, x[1:]):
        expected = Counter(prev[1])
        expected.subtract(prev[0])
        for chain in row:
            actual = Counter()
            for g in chain:
                actual.update(boundary(g))
            if actual != expected:
                return False
    return True


def verify(a, b):
    bases = defaultdict(set)
    for g in product(globe(a), globe(1), globe(b)):
        bases[sum(d for d, _ in g)].add(g)
    for k in range(a + b + 2):
        target = {y for y in strict_cells((a + 1, b + 1), k + 1) if y[0] == CORNERS}
        for y in target:
            x = section(a, b, y)
            assert valid(x, bases) and image(x) == y
            if k:
                assert all(face(x, d) == section(a, b, face(y, d)) for d in (0, 1))
        print(f'hom degree {k}: verified {len(target)} cells', flush=True)
    for p, q in product(globe(a), globe(b)):
        x = atom((p, (1, 2), q))
        assert section(a, b, image(x)) == x


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('a', type=int)
    parser.add_argument('b', type=int)
    args = parser.parse_args()
    if min(args.a, args.b) < 0:
        parser.error('dimensions must be nonnegative')
    verify(args.a, args.b)
