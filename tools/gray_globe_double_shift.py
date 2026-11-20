"""Check the two-degree section of the interior projection of a globe pair."""
import argparse
from collections import Counter
from functools import cache
from itertools import product

from gray_globe_comparison import atom, boundary, face, globe
from gray_globe_corner_pullback import labelled_tableaux
from gray_globe_cubical_corner import map_rows
from gray_globe_run_transport import peak, positions
from gray_globe_section import cells, trim


def opposite(tag):
    return 1-tag if tag < 2 else 2


@cache
def column(m, n, g):
    (r, x), (s, y) = g
    terms = [((r+1, x), (s+1, opposite(y)))]
    if s == 0 and r+2 <= m:
        terms.append(((r+2, x if r+2 < m else 2), (0, x ^ (r % 2))))
    if r == 0 and s+2 <= n:
        terms.append(((0, y), (s+2, y if s+2 < n else 2)))
    return tuple(terms)


def interior(g):
    (i, x), (j, y) = g
    return (((i-1, x), (j-1, opposite(y))),) if i and j else ()


def project(c):
    return trim(map_rows(c[2:], interior))


def section(m, n, c):
    return peak(m, n)[:2] + map_rows(c, lambda g: column(m, n, g))


def check(m, n):
    poles = peak(m, n)[:2]
    for g in product(globe(m-1), globe(n-1)):
        lhs = Counter()
        for h in column(m, n, g):
            lhs.update(boundary(h))
        rhs = Counter()
        if g[0][0] + g[1][0]:
            for h, sign in boundary(g).items():
                for item in column(m, n, h):
                    rhs[item] += sign
        else:
            rhs.update(poles[1][1])
            rhs.subtract(poles[1][0])
        assert lhs == rhs
    small = set(labelled_tableaux(m-1, n-1))
    big = {c for c in labelled_tableaux(m, n) if c[:2] == poles}
    if max(m,n) <= 5:
        assert big == {c for c in cells((m,n)) if c[:2] == poles}
    assert {project(c) for c in big} == small
    for c in small:
        larger = section(m, n, c)
        assert larger in big and project(larger) == c
        if len(c) > 1:
            assert all(section(m, n, face(c, i)) == face(larger, i) for i in (0, 1))
    tower = 0
    for c in big:
        k = max(m,n)+1
        if len(c) > k and len(c[k][0]) == len(positions(m, n, k)):
            assert section(m, n, project(c)) == c
            tower += 1
    assert section(m, n, peak(m-1, n-1)) == peak(m, n)
    print(f'D^{m} tensor D^{n}: {len(big)} cells in the double hom, {len(small)} section values, '
          f'{tower} cells recovered above the full mixed row.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    args = parser.parse_args()
    if min(args.m, args.n) < 2:
        parser.error('require both globe dimensions at least two')
    check(args.m, args.n)
