"""Recover alcove faces and a cubical torus by strict dominance."""

from collections import Counter
from itertools import combinations, permutations, product

from homotopy_polygraph_hubs import dominance_program


def lift(point):
    coords = (*point, 0)
    return tuple(len(coords) * x - sum(coords) for x in coords)


def column(face):
    return tuple(1 + max(coord) for coord in zip(*face))


def dominated(rows, bound):
    return frozenset(row for row in rows if all(a < b for a, b in zip(row, bound)))


def audit_alcoves():
    count = 0
    for dim in range(1, 5):
        rows = [lift(x) for x in product(range(-1, 3), repeat=dim)]
        for axes in permutations(range(dim)):
            point = [0] * dim
            vertices = [lift(point)]
            for axis in axes:
                point[axis] += 1
                vertices.append(lift(point))
            for size in range(1, dim + 2):
                for face in combinations(vertices, size):
                    assert dominated(rows, column(face)) == frozenset(face)
                    count += 1
    print(f'{count} alcove faces recovered among neighbouring lattice points.')


def torus():
    cubes = {(x, y, 0) for x, y in product(range(3), repeat=2) if (x, y) != (1, 1)}
    triangles = []
    for cube in cubes:
        for axis, sign in product(range(3), (-1, 1)):
            neighbour = list(cube)
            neighbour[axis] += sign
            if tuple(neighbour) in cubes:
                continue
            corner = list(cube)
            corner[axis] += int(sign > 0)
            free_axes = sorted(set(range(3)) - {axis})
            for order in permutations(free_axes):
                point = corner[:]
                face = [lift(point)]
                for k in order:
                    point[k] += 1
                    face.append(lift(point))
                triangles.append(frozenset(face))
    rows = sorted(set.union(set(), *triangles))
    for triangle in triangles:
        assert dominated(rows, column(triangle)) == triangle
    edges = Counter(edge for face in triangles for edge in combinations(sorted(face), 2))
    assert set(edges.values()) == {2}
    assert (len(rows), len(edges), len(triangles)) == (32, 96, 64)
    print('Four-coordinate torus: 32 vertices, 96 edges and 64 triangles.')

    # Run the actual control and visit-order construction on two adjacent facets.
    first = triangles[0]
    adjacent = next(face for face in triangles if len(face & first) == 2)
    vertices = sorted(first | adjacent)
    facets = dominance_program(vertices, [column(first), column(adjacent)])
    assert [frozenset(vertices[i] for i in facet) for facet in facets] == [first, adjacent]


if __name__ == '__main__':
    audit_alcoves()
    torus()
