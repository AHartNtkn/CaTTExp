"""Certify the finite path collapses extending the hexagon section to two arbitrary strings."""

from collections import Counter
from functools import cache
from itertools import product

from gray_globe_comparison import atom, close_atoms, face, globe
from gray_globe_section import trim
from gray_hexagon_section import CORNERS, HEXAGON, TOP, image, lift


def path(length):
    return [(0, i) for i in range(length+1)] + [(1, i) for i in range(length)]


def suspension(length):
    return [(0, 0), (0, 1)] + [(d+1, i) for d, i in path(length)]


def signed_faces(g, suspended):
    degree, i = g
    if not degree:
        return ()
    if suspended and degree == 1:
        return ((0, 0), (0, 1))
    return ((degree-1, i), (degree-1, i+1))


def differential(basis, target):
    result = Counter()
    for axis, g in enumerate(basis):
        sign = (-1)**sum(d for d, _ in basis[:axis])
        if axis == 1 and not target:
            terms = HEXAGON.boundary[g].items()
        else:
            faces = ((0, 0), (0, 1)) if axis == 1 and g[0] else signed_faces(g, target)
            terms = zip(faces, (-1, 1))
        for f, n in terms:
            result[basis[:axis] + (f,) + basis[axis+1:]] += sign*n
    return result


def source_diff(g):
    return differential(g, False)


def target_diff(g):
    return differential(g, True)


def project_axis(g, cut, suspended):
    degree, i = g
    if suspended and degree == 0:
        return g
    if degree == int(suspended):
        return (degree, int(i > cut))
    return (degree, 2) if i == cut else None


def projection(cell, i, j, target):
    def chain(row):
        terms = []
        for a, b, c in row:
            p = project_axis(a, i, target)
            q = project_axis(c, j, target)
            if p is not None and q is not None:
                terms.append((p, b, q))
        return tuple(sorted(terms))
    return tuple(tuple(chain(row) for row in pair) for pair in cell)


def inverse_terms(cut, value, length):
    degree, side = value
    if degree:
        return [((1, cut), 1)]
    if side == 1:
        return [((0, length), 1)] if cut == length-1 else []
    terms = [((0, cut), 1)]
    if cut+1 < length:
        terms.append(((0, cut+1), -1))
    return terms


@cache
def local(y):
    return lift(1, 1, y)


def recover(y, r, s):
    rows = [[Counter(), Counter()] for _ in y[1:]]
    tests = {}
    for i, j in product(range(r), range(s)):
        x = local(projection(y, i, j, True))
        tests[i, j] = x
        for accum, pair in zip(rows, x):
            for result, chain in zip(accum, pair):
                for a, h, b in chain:
                    for (p, u), (q, v) in product(inverse_terms(i, a, r), inverse_terms(j, b, s)):
                        result[p, h, q] += u*v
    assert all(chain >= Counter() for pair in rows for chain in pair)
    cell = tuple(tuple(tuple(sorted(chain.elements())) for chain in pair) for pair in rows)
    assert all(projection(cell, i, j, False) == value for (i, j), value in tests.items())
    return cell


def verify(r, s):
    source = {g: atom(g, source_diff) for g in product(path(r), HEXAGON.boundary, path(s))}
    target = [atom(g, target_diff) for g in product(suspension(r), globe(1), suspension(s))]
    source_cells = {trim(c) for c in close_atoms(source.values(), 4)}
    # Trimming identifies all identity paddings. Recheck one padding of each cell separately.
    targets = {trim(c) for c in close_atoms(target, 5) if c[0] == CORNERS}
    chosen = {}
    for y in sorted(targets, key=len):
        x = recover(y, r, s)
        assert x in source_cells and image(x) == y
        assert recover(y + (((), ()),), r, s) == x + (((), ()),)
        if len(x) > 1:
            for side in (0, 1):
                assert trim(face(x, side)) == chosen[trim(face(y, side))]
        chosen[y] = x
    for p, q in product(path(r), path(s)):
        source_atom = source[p, TOP, q]
        target_atom = atom(((p[0]+1, p[1]), (1, 2), (q[0]+1, q[1])), target_diff)
        assert chosen[target_atom] == source_atom
    print(f"[{r}] and [{s}]: {len(chosen)} diagonal cells, {len(path(r))*len(path(s))} atom pins", flush=True)


if __name__ == "__main__":
    for lengths in product((1, 2), repeat=2):
        verify(*lengths)
