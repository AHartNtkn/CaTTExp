"""Enumerate signed globe-pair tableaux from their maximal bidegrees and recover corner fibres."""
import argparse
from collections import defaultdict
from itertools import combinations, product, zip_longest
from math import comb

from gray_globe_comparison import atom
from gray_globe_factorizations import profile, rank
from gray_globe_section import EMPTY_ROW, cells, row_map
from gray_globe_strip_squares import minimal_shape



def labelled_tableaux(m, n):
    for count in range(1, min(m, n)+2):
        for a in combinations(range(m+1), count):
            for ascending in combinations(range(n+1), count):
                b = ascending[::-1]
                ranks = {(r, s) for u, v in zip(a, b) for r in range(u+1) for s in range(v+1)}
                rows = [sorted(p for p in ranks if sum(p) == k)
                        for k in range(max(map(sum, ranks))+1)]
                left_tags = (2,) if a[-1] == m else (0, 1)
                right_tags = (2,) if b[0] == n else (0, 1)
                for bits, x, y in product(product((0, 1), repeat=count-1), left_tags, right_tags):
                    right_bits = [(u % 2) ^ (1-t) for u, t in zip(a, bits)]
                    first = dict(zip(a, (*bits, x)))
                    second = dict(zip(b, (y, *right_bits)))

                    def entry(r, s, side):
                        left = side if (r+1, s) in ranks else first[r]
                        right = (r % 2) ^ side if (r, s+1) in ranks else second[s]
                        return (r, left), (s, right)
                    yield tuple(tuple(tuple(entry(r, s, side) for r, s in sites)
                                      for side in (0, 1)) for sites in rows)


def small_schroeder(n):
    # Dyck paths with a freely marked subset of their valleys.
    return sum(2**(k-1) * comb(n, k) * comb(n, k-1) for k in range(1, n+1)) // n


def collapse(cell, axis, cutoff):
    def image(g):
        r = g[axis][0]
        if r < cutoff:
            return g
        if r == cutoff:
            return g[:axis] + ((r, 2),) + g[axis+1:]
        return None
    return row_map(cell, 0, image)


def recover(left, right, i, j):
    def chain(l, r):
        entries = [g for g in l if g[1][0] < j]
        entries.extend(g for g in r if g[0][0] < i and g[1][0] >= j)
        x = [p for p, q in l if (p[0], q[0]) == (i, j)]
        y = [q for p, q in r if (p[0], q[0]) == (i, j)]
        assert len(x) == len(y) <= 1
        entries.extend(zip(x, y))
        return tuple(sorted(entries))
    return tuple(tuple(chain(a, b) for a, b in zip(l, r))
                 for l, r in zip_longest(left, right, fillvalue=EMPTY_ROW))


def corner_cells(m, n, i, j):
    return {c for c in cells((m, n)) if
            not (profile(c) & {(i+1, j), (i, j+1)}) and c}


def check(m, n, i, j):
    diagrams = list(labelled_tableaux(m, n))
    assert len(set(diagrams)) == len(diagrams) and set(diagrams) == cells((m, n)) - {()}
    print(f'Full globe pair: {len(diagrams)} distinct tableaux reconstructed from maximal sites')
    left = corner_cells(m, j, i, j)
    right = corner_cells(i, n, i, j)
    fibre = defaultdict(list)
    for r in right:
        fibre[collapse(r, 1, j)].append(r)
    target = corner_cells(m, n, i, j)
    lifted = set()
    for l in left:
        for r in fibre[collapse(l, 0, i)]:
            w = recover(l, r, i, j)
            assert collapse(w, 1, j) == l and collapse(w, 0, i) == r
            lifted.add(w)
    assert lifted == target

    def singles(domain):
        return {w for w in domain if len(w) == i+j+1 and
                len(w[-1][0]) == 1 and rank(w[-1][0][0]) == (i, j)}

    a, b, all_steps = map(singles, (left, right, target))
    assert {recover(l, r, i, j) for l, r in product(a, b)} == all_steps
    assert len(a) * len(b) == len(all_steps)
    shapes = tuple({minimal_shape(w) for w in group} for group in (a, b, all_steps))
    assert {recover(l, r, i, j) for l, r in product(*shapes[:2])} == shapes[2]
    print(f'Corner ({i},{j}) in ({m},{n}): {len(lifted)} cells; '
          f'{len(a)} x {len(b)} = {len(all_steps)} labelled single steps; '
          f'{len(shapes[0])} x {len(shapes[1])} = {len(shapes[2])} face shapes')
    if min(m, n) >= i+j-1:
        assert len(shapes[0]) == small_schroeder(j) and len(shapes[1]) == small_schroeder(i)
    for group in (a, b):
        for w in group:
            assert collapse(collapse(w, 0, i), 1, j) == atom(((i, 2), (j, 2)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ('m', 'n', 'i', 'j'):
        parser.add_argument(key, type=int)
    args = parser.parse_args()
    if not (1 <= args.i <= args.m and 1 <= args.j <= args.n):
        parser.error('the positive corner must lie in the globe pair')
    check(args.m, args.n, args.i, args.j)
