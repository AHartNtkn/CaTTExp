"""Check the pinned globular section for two suspended paths of given lengths."""
import argparse
from collections import Counter, defaultdict
from itertools import product

from gray_globe_comparison import CORNERS, atom, close_atoms, face, image


def differential(basis, suspended):
    result = Counter()
    sign = 1
    for i, (degree, label) in enumerate(basis):
        if degree:
            low, high = (0, 1) if suspended and degree == 1 else (label, label + 1)
            for vertex, coefficient in [(low, -1), (high, 1)]:
                key = basis[:i] + ((degree - 1, vertex),) + basis[i + 1:]
                result[key] += sign * coefficient
        sign *= (-1) ** degree
    return result


def grid_boundary(basis):
    return differential(basis, False)


def suspended_boundary(basis):
    return differential(basis, True)


def path(length):
    return [(0, i) for i in range(length + 1)] + [(1, i) for i in range(length)]


def ordered_word(arrow):
    """Read a source-grid tableau as a word in P=0, M=1 and Q=2."""
    vertex = arrow[0][0][0]
    outgoing = {}
    for edge in arrow[1][0]:
        start = tuple((0, i) for _, i in edge)
        assert start not in outgoing
        outgoing[start] = edge
    word = []
    while vertex in outgoing:
        edge = outgoing.pop(vertex)
        word.append(next(i for i, (degree, _) in enumerate(edge) if degree))
        vertex = atom(edge, grid_boundary)[0][1][0]
    assert not outgoing and vertex == arrow[0][1][0]
    return word


def normal(arrow):
    previous = -1
    for axis in ordered_word(arrow):
        if axis == 1:
            previous = -1
        elif axis < previous:
            return False
        else:
            previous = axis
    return True


def with_boundaries(left, right, chain):
    assert left[:-1] == right[:-1]
    top = tuple(sorted(chain))
    return left[:-1] + ((left[-1][0], right[-1][0]), (top, top))


def lift_two(cell, left, right):
    word = ordered_word(left)
    origin = tuple(i for _, i in left[0][0][0])
    squares = []

    def position(index):
        return tuple(offset + word[:index].count(axis) for axis, offset in enumerate(origin))

    def swap(index):
        a, b = word[index:index + 2]
        assert a > b
        squares.append(tuple((int(axis in (a, b)), x)
                             for axis, x in enumerate(position(index))))
        word[index:index + 2] = [b, a]

    steps = {}
    for (d, i), (e, j) in cell[-1][0]:
        assert (d, e) in ((2, 1), (1, 2))
        start = (i, j) if d == 2 else (i, j + 1)
        assert start not in steps
        steps[start] = 0 if d == 2 else 2
    while steps:
        middle = word.index(1)
        i, _, j = position(middle)
        if steps.pop((i, j)) == 0:
            swap(middle)
            while middle and word[middle - 1] == 2:
                swap(middle - 1)
                middle -= 1
        else:
            swap(middle - 1)
            while middle + 1 < len(word) and word[middle + 1] == 0:
                swap(middle)
                middle += 1
    assert word == ordered_word(right)
    return with_boundaries(left, right, squares)


def path_section(r, s):
    if min(r, s) < 0:
        raise ValueError('path lengths must be nonnegative')
    paths = path(r), path(s)
    source_atoms = {atom(b, grid_boundary) for b in product(paths[0], path(1), paths[1])}
    suspended = [[(0, 0), (0, 1)] + [(d + 1, i) for d, i in p] for p in paths]
    target_atoms = {atom(b, suspended_boundary) for b in product(*suspended)}
    lifts = {}
    for degree in range(4):
        source = close_atoms(source_atoms, degree)
        target = {y for y in close_atoms(target_atoms, degree + 1) if y[0] == CORNERS}
        candidates = defaultdict(list)
        if degree <= 1:
            for x in source:
                if degree == 0 or normal(x):
                    candidates[image(x)].append(x)
        for y in target:
            if degree <= 1:
                x, = candidates[y]
            else:
                left, right = [lifts[face(y, side)] for side in (0, 1)]
                if degree == 2:
                    x = lift_two(y, left, right)
                else:
                    cubes = []
                    for (a, i), (b, j) in y[-1][0]:
                        assert a == b == 2
                        cubes.append(((1, i), (1, 0), (1, j)))
                    x = with_boundaries(left, right, cubes)
            assert x in source and image(x) == y
            if degree:
                assert all(face(x, side) == lifts[face(y, side)] for side in (0, 1))
            lifts[y] = x
    for p, q in product(*paths):
        mixed = atom((p, (1, 0), q), grid_boundary)
        target = atom(((p[0] + 1, p[1]), (q[0] + 1, q[1])), suspended_boundary)
        assert lifts[target] == mixed
    return lifts


def verify(r, s):
    counts = Counter(len(y) - 2 for y in path_section(r, s))
    return [counts[k] for k in range(4)]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('r', type=int)
    parser.add_argument('s', type=int)
    args = parser.parse_args()
    print('Cells checked in hom degrees 0 through 3:', *verify(args.r, args.s))
