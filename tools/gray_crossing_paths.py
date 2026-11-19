"""Check the square comparison for the two path boundaries of a globe tensor."""
import argparse
from collections import Counter, defaultdict
from itertools import product

from gray_globe_comparison import atom, face, globe, image as suspend_image
from gray_globe_section import cells, omit, row_map, section, trim
from gray_hexagon_section import (ROUTES, TOP, image as hexagon_image,
                                  lift as hexagon_lift, source_atoms)


def reverse_tag(label):
    rank, tag = label
    return rank, 1 - tag if tag < 2 else tag


def coordinates(cell):
    """Extract the two cylinder margins and the twice-desuspended mixed rows."""
    def left(basis):
        (p, s), (q, t) = basis
        if p >= 2 and q <= 1:
            return (p-2, s), (q, 2 if q else t)

    def right(basis):
        (p, s), (q, t) = basis
        if q >= 2 and p <= 1:
            return (p, 2 if p else s), (q-2, t)

    def middle(basis):
        (p, s), (q, t) = basis
        if p and q:
            return (p-1, s), reverse_tag((q-1, t))

    return tuple(row_map(cell, 2, f) for f in (left, right, middle))


def left_quotient(basis):
    p, time = basis
    if time[0]:
        return p[0]+1, p[1]
    if p[0] == 0:
        return time


def right_quotient(basis):
    time, q = basis
    if time[0]:
        return reverse_tag((q[0]+1, q[1]))
    if q[0] == 0:
        return time


def square_image(cell):
    left = omit(omit(cell, 3, 0), 2, 0)
    right = omit(omit(cell, 0, 0), 0, 0)

    def tensor_quotient(basis):
        p, q = left_quotient(basis[:2]), right_quotient(basis[2:])
        if p is not None and q is not None:
            return p, q

    return left, right, row_map(cell, 0, tensor_quotient)


def pullback(a, b):
    def by_quotient(shape, quotient):
        groups = defaultdict(list)
        for x in cells(shape):
            if x:
                groups[row_map(x, 0, lambda g: (z,) if (z := quotient(g)) is not None
                               else None)].append(x)
        return groups

    left = by_quotient((a, 1), left_quotient)
    right = by_quotient((1, b), right_quotient)
    return {(u, v, w) for w in cells((a+1, b+1)) if w
            for u in left[omit(w, 1, 0)] for v in right[omit(w, 0, 0)]}


def square_vertex(word):
    return (0, int(word.index('A') < word.index('B'))), (0, int(word.index('B') < word.index('C')))


def collapse_hexagon(cell):
    def collapse(basis):
        p, h, q = basis
        degree, (route, step) = h
        if h == TOP:
            square = ((1, 2), (1, 2))
        elif degree == 0:
            word = ROUTES[route][step] if route < 2 else ROUTES[0][3*step]
            square = square_vertex(word)
        else:
            before, after = map(square_vertex, ROUTES[route][step:step+2])
            if before == after:
                return None
            square = tuple(x if x == y else (1, 2) for x, y in zip(before, after))
        return (p, *square, q)

    return row_map(cell, 0, collapse)


def verify(a, b):
    top = atom(((a+2, 2), (b+2, 2)))
    target = {y for y in cells((a+2, b+2)) if y[:2] == top[:2]}
    decoded = {coordinates(y): y for y in target}
    assert len(decoded) == len(target) and decoded.keys() == pullback(a, b)
    for x in source_atoms(a, b).values():
        assert square_image(collapse_hexagon(x)) == coordinates(suspend_image(hexagon_image(x)))

    squares = cells((a, 1, 1, b))
    chosen = {}
    for y in sorted(target, key=len):
        first = section(a+1, b+1, y)
        x = collapse_hexagon(hexagon_lift(a, b, first))
        assert x in squares and len(x) == len(y)-2 and square_image(x) == coordinates(y)
        if len(x) > 1:
            for side in (0, 1):
                assert trim(face(x, side)) == chosen[trim(face(y, side))]
        chosen[y] = x
    for p, q in product(globe(a), globe(b)):
        y = atom(((p[0]+2, p[1]), (q[0]+2, q[1])))
        assert chosen[y] == atom((p, (1, 2), (1, 2), q))

    counts = Counter(len(y)-3 for y in target)
    print(f'D^{a+2} x D^{b+2}, nonidentity cells by hom degree (including objects): '
          f'{[counts[d] for d in sorted(counts)]}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('a', type=int, help='first globe dimension minus two')
    parser.add_argument('b', type=int, help='second globe dimension minus two')
    args = parser.parse_args()
    if min(args.a, args.b) < 0:
        parser.error('both arguments must be nonnegative')
    verify(args.a, args.b)
