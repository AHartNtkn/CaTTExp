"""Cubical projection, path comparison, and recursive globular section for full upper rows of globe pairs."""
import argparse
from collections import Counter
from functools import cache
from itertools import product

from gray_globe_comparison import atom, boundary, face
from gray_globe_section import EMPTY_ROW, cells, trim
from gray_path_wedge import compose


def cube_label(bits):
    # The displayed positions increase from left to right; Gray tensor order decreases.
    return tuple((int(x == 2), x) for x in reversed(bits))


def symbols(label):
    return tuple(x for _, x in reversed(label))


def corner(m, n, h, w):
    """Normalize the full row to a bit vertex and each higher label to its decorated interval."""
    assert 0 <= h <= min(m, n)
    k, offset = m+n-h, m-h
    assert w[:k] == atom(((m, 2), (n, 2)))[:k]
    def vertex(chain):
        assert [i for (i, _), _ in chain] == list(range(offset, m+1))
        return (tuple(bit for (_, bit), _ in chain[:-1]),)
    def label(g):
        (i, right), (j, tag) = g
        a, b = n-j+1, i-offset
        return a, b, tag ^ ((offset+a-1) % 2) if a > 1 else 2, right
    return (tuple(vertex(chain) for chain in w[k]),) + tuple(
        tuple(tuple(label(g) for g in chain) for chain in row) for row in w[k+1:])


def interval_image(g):
    z = symbols(g)
    moving = [i for i, x in enumerate(z) if x == 2]
    if not moving:
        return (z,)
    a, b = moving[0], moving[-1]
    if len(moving) != b-a+1:
        return ()
    return ((a+1, b+1, z[a-1] if a else 2, z[b+1] if b+1 < len(z) else 2),)


def map_rows(w, image):
    return tuple(tuple(tuple(sorted(y for g in chain for y in image(g))) for chain in row) for row in w)


def project(w):
    return trim(map_rows(w, interval_image))


def projected_chain(m, n, h, g):
    offset = m-h
    def label(a, b, left, right):
        j = n-a+1
        tag = left ^ ((offset+a-1) % 2) if j < n else 2
        return ((offset+b, right), (j, tag))
    z = symbols(g)
    if 2 not in z:
        return tuple(label(b+1, b, z[b-1] if b else 2, z[b] if b < h else 2)
                     for b in range(h+1))
    return tuple(label(*q) for q in interval_image(g))


def check_projection(m, n, h):
    k = m+n-h
    lower = atom(((m, 2), (n, 2)))[k-1]
    for z in product(range(3), repeat=h):
        g = cube_label(z)
        lhs, rhs = Counter(), Counter()
        for q in projected_chain(m, n, h, g):
            lhs.update(boundary(q))
        if 2 in z:
            for f, sign in boundary(g).items():
                for q in projected_chain(m, n, h, f):
                    rhs[q] += sign
        else:
            rhs.update(lower[1])
            rhs.subtract(lower[0])
        assert lhs == rhs


@cache
def path_image(g):
    """Linear image of a face of the cube of joins, in degree one higher."""
    components = [[[0]]]
    for j, bit in enumerate(symbols(g), 1):
        if bit == 0:
            components.append([[j]])
        elif bit == 1:
            components[-1][-1].append(j)
        else:
            components[-1].append([j])
    h = len(g)+1
    active = [i for i, c in enumerate(components) if len(c) > 1]
    if len(active) > 1:
        return ()
    out = []
    for i in active or range(len(components)):
        blocks = components[i]
        for chosen in product(*blocks):
            z = [int(j < blocks[0][0]) for j in range(h)]
            for block, p in zip(blocks, chosen):
                for j in block:
                    z[j] = 2 if j == p else int(j > p)
            out.append(cube_label(z))
    return tuple(sorted(out))


def path_comparison(w, h):
    endpoints = tuple((cube_label((s,)*h),) for s in (0, 1))
    return trim((endpoints,) + map_rows(w, path_image))


def diagonal(w):
    """Forget the common two poles; number the joins between letters as new positions."""
    def vertex(chain):
        return (tuple(right for _, _, _, right in chain[:-1]),)
    def lower(c):
        a, b, left, right = c
        return a, b-1, 1-left if left != 2 else 2, right
    return (tuple(vertex(chain) for chain in w[1]),) + map_rows(w[2:], lambda c: (lower(c),))


def restrict_run(w, start, stop):
    def interval(c):
        a, b, left, right = c
        if a < start or b > stop:
            return ()
        return ((a-start+1, b-start+1, left if a > start else 2, right if b < stop else 2),)
    return trim((tuple((chain[0][start-1:stop],) for chain in w[0]),) + map_rows(w[1:], interval))


@cache
def section(w):
    (s,), (t,) = w[0]
    if len(w) == 1:
        return atom(cube_label(s))
    moving = [i for i, (a, b) in enumerate(zip(s, t), 1) if a != b]
    assert moving and all(s[i-1] == 0 and t[i-1] == 1 for i in moving)
    h = len(s)
    if len(moving) == h:
        return path_comparison(section(diagonal(w)), h)
    runs = []
    for i in moving:
        if runs and runs[-1][1] == i-1:
            runs[-1] = runs[-1][0], i
        else:
            runs.append((i, i))
    result = None
    for a, b in runs:
        lifted = section(restrict_run(w, a, b))
        labels = lambda g: (cube_label(t[:a-1]+symbols(g)+s[b:]),)
        padded = map_rows(lifted, labels) + (EMPTY_ROW,)*(len(w)-len(lifted))
        result = padded if result is None else compose(result, padded, 0)
    return trim(result)


def check_path_differential(h):
    for z in product(range(3), repeat=h-1):
        g = cube_label(z)
        lhs = Counter()
        for y in path_image(g):
            lhs.update(boundary(y))
        rhs = Counter()
        if 2 in z:
            for y, sign in boundary(g).items():
                for t in path_image(y):
                    rhs[t] += sign
        else:
            rhs = Counter({cube_label((1,)*h): 1, cube_label((0,)*h): -1})
        assert lhs == rhs


def check(m, n, h, exhaustive_cube):
    check_projection(m, n, h)
    check_path_differential(h)
    for z in product(range(3), repeat=h-1):
        c = atom(cube_label(z))
        assert diagonal(project(path_comparison(c, h))) == project(c)
    k = m+n-h
    # Use the peak presentation for larger rectangles to avoid closure under all compositions.
    from gray_globe_corner_pullback import labelled_tableaux
    domain = (labelled_tableaux(m, n) if max(m, n) > 5 else cells((m, n)))
    full = {w for w in domain if len(w) > k and len(w[k][0]) == h+1}
    intrinsic = {corner(m, n, h, w) for w in full}
    assert len(intrinsic) == len(full)
    if exhaustive_cube:
        cube = cells((1,)*h)-{()}
        assert {project(w) for w in cube} == intrinsic
        assert all(section(w) in cube for w in intrinsic)
    for w in intrinsic:
        result = section(w)
        assert project(result) == w and len(result) == len(w)
        if len(w) > 1:
            assert all(section(face(w, i)) == face(result, i) for i in (0, 1))
    pinned = 0
    for z in product(range(3), repeat=h):
        g = cube_label(z)
        if interval_image(g):
            c = atom(g)
            assert section(project(c)) == c
            pinned += 1
    print(f'D^{m} tensor D^{n}, full row {k}: {len(full)} cells, {pinned} cubical pins; '
          f'all faces and right-inverse equations checked.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    parser.add_argument('h', type=int, help='number of bit coordinates on the full row')
    parser.add_argument('--exhaustive-cube', action='store_true', help='also enumerate the whole source cube')
    args = parser.parse_args()
    if not 1 <= args.h <= min(args.m, args.n):
        parser.error('require 1 <= h <= min(m,n)')
    check(args.m, args.n, args.h, args.exhaustive_cube)
