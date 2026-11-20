"""Certify the two path windows used at a pair of nodes in the hexagon section."""

from collections import Counter, defaultdict
from functools import cache
from itertools import product

from gray_globe_comparison import atom, close_atoms, face, globe
from gray_globe_section import omit, reverse, row_map, trim
from gray_hexagon_paths import inverse_terms, path, project_axis, source_diff
from gray_hexagon_section import (HEXAGON, TOP, crossing, local_table, outer_signature,
                                  outer_table, signature)
from gray_tree_section import reflect


@cache
def project(cell, cuts):
    def basis(g):
        result = list(g)
        for axis, length, cut in cuts:
            result[axis] = project_axis(g[axis], cut, False) if length else (0, 2)
            if result[axis] is None:
                return None
        return tuple(result)
    return row_map(cell, 0, basis)


def inverse(length, cut, value):
    return inverse_terms(cut, value, length) if length else [((0, 0), 1)]


def recover(r, s, choose):
    rows = [[Counter(), Counter()] for _ in range(5)]
    tests = {}
    for i, j in product(range(max(1, r)), range(max(1, s))):
        test = choose(i, j)
        tests[i, j] = test
        for pair, signed in zip(rows, test):
            for result, chain in zip(pair, signed):
                for p, h, q in chain:
                    for (a, n), (b, m) in product(inverse(r, i, p), inverse(s, j, q)):
                        result[a, h, b] += n*m
    assert all(chain >= Counter() for pair in rows for chain in pair)
    cell = trim(tuple(tuple(tuple(sorted(chain.elements())) for chain in pair) for pair in rows))
    assert all(project(cell, ((0, r, i), (2, s, j))) == test for (i, j), test in tests.items())
    return cell


@cache
def select_window(r, s, u, v, w):
    unit = local_table(int(r > 0), int(s > 0))

    def choose(i, j):
        return unit[project(u, ((0, r, i),)), project(v, ((1, s, j),)),
                    project(w, ((0, r, i), (2, s, j)))]
    return recover(r, s, choose)


@cache
def select_outer(length, left, h, w):
    unit = outer_table(int(length > 0), left)
    if left:
        return recover(length, 0, lambda i, j: unit[h, project(w, ((0, length, i),))])
    return recover(0, length, lambda i, j: unit[h, project(w, ((2, length, j),))])


@cache
def cells(r, s):
    atoms = [atom(g, source_diff) for g in product(path(r), HEXAGON.boundary, path(s))]
    return {trim(t) for t in close_atoms(atoms, 4)} | {()}


def grids(axes):
    """None denotes the globe-tagged interval in the unit table."""
    def differential(g):
        result = Counter()
        sign = 1
        for j, (degree, label) in enumerate(g):
            if degree:
                vertex = 0 if axes[j] is None else label
                for side in (0, 1):
                    result[g[:j] + ((0, vertex + side),) + g[j+1:]] += sign*(2*side-1)
            sign *= (-1)**degree
        return result
    atoms = [atom(g, differential) for g in product(*(globe(1) if n is None else path(n) for n in axes))]
    return {trim(t) for t in close_atoms(atoms, 3)} | {()}


def verify_faces_and_pins(chosen, key, r, s):
    for x in chosen.values():
        if len(x) > 1:
            for side in (0, 1):
                boundary = trim(face(x, side))
                assert chosen[key(boundary)] == boundary
    for p, q in product(path(r), path(s)):
        x = atom((p, TOP, q), source_diff)
        assert chosen[key(x)] == x


def verify_window(r, s):
    us, vs, ws = defaultdict(set), defaultdict(set), defaultdict(set)
    for x in cells(r, 0):
        u = omit(x, 2, 0)
        us[omit(u, 0, 0)].add(u)
    for x in cells(0, s):
        v = omit(x, 0, 0)
        vs[omit(v, 1, 0)].add(v)
    for t in grids((r, None, s)):
        w = row_map(t, 0, lambda g: (g[0], reverse(g[1]), reflect(g[2], s)))
        ws[omit(w, 2, 0), omit(w, 0, 0)].add(w)
    options = cells(r, s)
    chosen = {}
    for h in us:
        for u, v in product(us[h], vs[h]):
            for w in ws[crossing(u, 1), crossing(v, 0)]:
                x = select_window(r, s, u, v, w)
                assert x in options and signature(x) == (u, v, w)
                chosen[u, v, w] = x
    verify_faces_and_pins(chosen, signature, r, s)
    print(f'Window [{r}], [{s}]: {len(chosen)} compatible triples', flush=True)


def verify_outer(length, left):
    r, s = (length, 0) if left else (0, length)
    axis = 0 if left else 2
    by_margin = defaultdict(set)
    for t in grids((length, None, None) if left else (None, None, length)):
        w = row_map(t, 0, lambda g: (g[0], reverse(g[1]), reverse(g[2]))) if left else t
        by_margin[omit(w, axis, 0)].add(w)
    chosen = {}
    options = cells(r, s)
    for point in cells(0, 0):
        h, fixed = outer_signature(point, left)
        for w in by_margin[omit(fixed, axis, 0)]:
            x = select_outer(length, left, h, w)
            assert x in options and outer_signature(x, left) == (h, w)
            chosen[h, w] = x
    verify_faces_and_pins(chosen, lambda x: outer_signature(x, left), r, s)
    print(f'Outer [{length}], {"left" if left else "right"}: {len(chosen)} compatible pairs', flush=True)


if __name__ == '__main__':
    for n, left in product(range(3), (False, True)):
        verify_outer(n, left)
    for r, s in product(range(3), repeat=2):
        verify_window(r, s)
