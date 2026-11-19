"""Check moving-seam cylinders against strict closure in K ⊗ (P ∨ Q)."""
import argparse
import json
from collections import Counter, defaultdict
from functools import cache
from itertools import product

from gray_globe_comparison import atom, close_atoms
from gray_tree_section import generators, tree_boundary


@cache
def project_row(row):
    """Project the spatial factor to a point."""
    return tuple(sorted(g[:-1] for g in row if not g[-1][0]))


def project(table):
    return tuple(tuple(project_row(row) for row in pair) for pair in table)


def add_scaled(target, source, scale):
    for basis, coefficient in source.items():
        target[basis] += scale * coefficient


@cache
def basis_boundary(basis):
    return tree_boundary(basis)


def differential(chain):
    result = Counter()
    for g, coefficient in chain.items():
        add_scaled(result, basis_boundary(g), coefficient)
    return result


def cut_row(row, z):
    """Three edge columns and the two interior vertex columns of the cylinder."""
    edges = [Counter(), Counter(), Counter()]
    vertices = [Counter(), Counter()]
    for g, coefficient in row.items():
        address, label = g[-1]
        if not address:
            segment = 0 if label < z else 2 if label > z else 1
        else:
            segment = 0 if address[0] < z else 2
        edges[segment][g] += coefficient
        if len(address) == 1 and address[0] in (z - 1, z):
            vertices[address[0] - z + 1][g[:-1] + (((), z),)] += coefficient
    return edges, vertices


def cylinder(left, right, common, z):
    """Verify the differential of every generator of D^n ⊗ [3], even for signed rows."""
    endpoints = left[0][0], right[0][1]
    table = [endpoints]
    previous = None
    first_negative = None
    for degree in range(1, len(left)):
        current, output = [], []
        for l, r, shared in zip(left[degree], right[degree], common[degree]):
            row = Counter(l + r)
            row.subtract(g + (((), z),) for g in shared)
            edges, inner = cut_row(row, z)
            vertices = [Counter(endpoints[0]) if degree == 1 else Counter(),
                        *inner, Counter(endpoints[1]) if degree == 1 else Counter()]
            assert all(v >= Counter() for v in vertices)
            assert edges[0] >= Counter() and edges[2] >= Counter()
            if first_negative is None and not edges[1] >= Counter():
                first_negative = degree
            columns = vertices + edges
            for i, column in enumerate(columns):
                expected = Counter()
                if previous is not None:
                    add_scaled(expected, previous[1][i], 1)
                    add_scaled(expected, previous[0][i], -1)
                if i >= 4:
                    j = i - 4
                    sign = (-1) ** (degree - 1)
                    add_scaled(expected, vertices[j + 1], sign)
                    add_scaled(expected, vertices[j], -sign)
                assert differential(column) == expected
            if degree == 1:
                assert all(sum(v.values()) == 1 for v in vertices)
            current.append(columns)
            output.append(tuple(sorted(row.elements())))
        previous = current
        table.append(tuple(output))
    return tuple(table), first_negative


def verify(clock, p, q):
    if not p or not q:
        raise ValueError('both wedge factors must contain an edge')
    z = len(p)
    left = generators(p)
    right = [((address[0] + z,) + address[1:], vertex) if address else ((), vertex + z)
             for address, vertex in generators(q)]
    clocks = list(product(*(generators(factor) for factor in clock)))

    def atoms(space):
        return {atom(k + (s,), tree_boundary, len) for k, s in product(clocks, space)}

    def limits(table):
        return table[0][0][0][-1][1], table[0][1][0][-1][1]

    left_atoms, right_atoms = atoms(left), atoms(right)
    whole_atoms = left_atoms | right_atoms
    for degree in range(1, max(map(len, whole_atoms)) + 1):
        group = defaultdict(list)
        for l in close_atoms(left_atoms, degree):
            a, b = limits(l)
            if a < z == b:
                group[project(l)].append(l)
        recovered, failures = set(), Counter()
        for r in close_atoms(right_atoms, degree):
            a, b = limits(r)
            if a != z or b <= z:
                continue
            shared = project(r)
            for l in group[shared]:
                h, negative = cylinder(l, r, shared, z)
                if negative is None:
                    assert h not in recovered
                    recovered.add(h)
                else:
                    failures[negative] += 1
        whole = {h for h in close_atoms(whole_atoms, degree)
                 if limits(h)[0] < z < limits(h)[1]}
        assert recovered == whole
        print(f'Degree {degree}: {len(whole)} crossing cells, '
              f'first negative row counts {dict(sorted(failures.items()))}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('clock', type=json.loads, help='list of Batanin trees for K')
    parser.add_argument('p', type=json.loads)
    parser.add_argument('q', type=json.loads)
    args = parser.parse_args()
    verify(args.clock, args.p, args.q)
