"""Check extensions of a globe-pair section by one maximal bidegree."""
import argparse
from collections import Counter
from functools import cache
from itertools import accumulate

from gray_globe_comparison import atom, boundary, face
from gray_globe_factorizations import orders, profile, rank, truncate
from gray_globe_section import EMPTY_ROW, cells, trim
from gray_path_wedge import compose


@cache
def blocks(c, point):
    """Split at d-1 into at most three factors, keeping the new d-label isolated."""
    i, j = point
    cut = i+j-1
    upper = {rank(g) for neg, _ in c[cut+1:] for g in neg}
    assert point in upper and (i+1, j) not in upper and (i, j+1) not in upper
    owner = {p: (p[0] > i) - (p[0] < i) for p in upper}
    assert {p for p in upper if owner[p] == 0} == {point}
    return ordered_factors(c, cut, owner)


def ordered_factors(c, cut, owner):
    """Assign whole groups in precedence order and reconstruct their shared faces."""
    precedences = orders(c, cut, owner)
    pending = set(owner.values())
    source = c[cut][0]
    result = []
    while pending:
        group = min(g for g in pending if not any(a in pending and b == g
                                                  for a, b in precedences))
        pending.remove(group)
        rows = [tuple(tuple(g for g in chain if owner[rank(g)] == group) for chain in row)
                for row in c[cut+1:]]
        target = Counter(source)
        for g in rows[0][0]:
            target.update(boundary(g))
        assert all(n >= 0 for n in target.values())
        target = tuple(sorted(target.elements()))
        result.append(trim(c[:cut] + ((source, target),) + tuple(rows)))
        source = target
    assert source == c[cut][1]
    return tuple(result)


def verify(m, n, all_points):
    counts = Counter()
    padded = set()
    kinds = Counter()
    for c in cells((m, n)) - {()}:
        ranks = profile(c)
        corners = {p for p in ranks if min(p) >= 1 and (p[0]+1, p[1]) not in ranks
                   and (p[0], p[1]+1) not in ranks}
        for point in (corners if all_points else corners & {(2, 2)}):
            d = sum(point)
            pieces = blocks(c, point)
            central, = (p for p in pieces if point in profile(p))
            assert len(central) == d+1 and len(central[-1][0]) == 1
            assert rank(central[-1][0][0]) == point
            height = len(c)
            def paste(x, y):
                assert x[:d-1] == y[:d-1] and x[d-1][1] == y[d-1][0]
                return compose(x + (EMPTY_ROW,)*(height-len(x)),
                               y + (EMPTY_ROW,)*(height-len(y)), d-1)
            assert list(accumulate(pieces, paste))[-1] == c
            for side in (0, 1):
                if len(c)-1 > d:
                    assert blocks(face(c, side), point) == tuple(
                        truncate(p, len(c)-2, side) for p in pieces)
                else:
                    assert face(c, side) == face(pieces[0 if side == 0 else -1], side)
            counts[point] += 1
            if point == (2, 2):
                kinds[len(c)-1] += 1
                padded.add(central)
    atoms = sum(w == atom(w[-1][0][0]) for w in padded)
    print(f'D^{m} tensor D^{n}: {sum(counts.values())} cell/attachment pairs checked')
    print('New (2,2)-cells by degree:', dict(sorted(kinds.items())))
    print(f'{atoms} atomic and {len(padded)-atoms} padded central 4-cells')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    parser.add_argument('--all-points', action='store_true')
    args = parser.parse_args()
    if min(args.m, args.n) < 0:
        parser.error('globe dimensions must be nonnegative')
    verify(args.m, args.n, args.all_points)
