"""Integral incidence checks for the seven-vertex seam obstruction."""
from collections import Counter
from itertools import combinations, permutations
from math import factorial


def orientation(order):
    inversions = sum(left > right for left, right in combinations(order, 2))
    return (-1) ** inversions


def flags(axes, start=0):
    for order in permutations(axes):
        vertices = [start]
        for axis in order:
            vertices.append(vertices[-1] | (1 << axis))
        yield tuple(vertices), orientation(order)


def face_cubes(vertices):
    """Top cubes [singleton, all vertices] in an oriented simplex."""
    for i, vertex in enumerate(vertices):
        yield (vertex, vertices), (-1) ** i


def facets(vertices):
    for i in range(len(vertices)):
        yield vertices[:i] + vertices[i + 1:], (-1) ** i


def nonzero(counter):
    return {cell: value for cell, value in counter.items() if value}


def check_six_seams():
    axes = tuple(range(6))
    total = Counter()
    chart_flags = list(flags(axes))
    for vertices, simplex_sign in chart_flags:
        for face, face_sign in facets(vertices):
            for piece, piece_sign in face_cubes(face):
                total[piece] += simplex_sign * face_sign * piece_sign

    expected = Counter()
    for i in axes:
        others = tuple(axis for axis in axes if axis != i)
        for side in (0, 1):
            facet_sign = (-1) ** i * (2 * side - 1)
            for face, local_sign in flags(others, side << i):
                for piece, piece_sign in face_cubes(face):
                    expected[piece] += facet_sign * local_sign * piece_sign
    assert nonzero(total) == nonzero(expected)
    assert len(nonzero(total)) == 12 * factorial(5) * 6
    assert set(nonzero(total).values()) == {-1, 1}

    ranks = tuple(range(7))
    interior_tests = 0
    endpoint_tests = 0
    for n in range(1, len(ranks)):
        for subset in combinations(ranks, n):
            images = Counter()
            for vertices, sign in chart_flags:
                image = tuple(vertices[j] for j in subset)
                images[image] += sign
                if 0 not in subset or 6 not in subset:
                    # The image has a common positive or a common negative bit.
                    assert image[0] or image[-1] != 63
            if any(j not in subset for j in range(1, 6)):
                assert not nonzero(images)
                interior_tests += 1
            else:
                endpoint_tests += 1
    print(f"{len(chart_flags)} oriented flags; {len(nonzero(total))} exterior five-cubes.")
    print(f"{interior_tests} proper rank subsets cancel in pairs; "
          f"{endpoint_tests} others factor through exterior facets.")


if __name__ == "__main__":
    check_six_seams()
