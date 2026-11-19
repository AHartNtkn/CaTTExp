"""Check the bounded face corrections for gluing two strips of a globe pair."""
import argparse
from collections import Counter
from functools import cache

from gray_globe_factorizations import hole_split, profile, truncate
from gray_globe_section import cells, row_map


@cache
def ranks(c):
    return frozenset(profile(c))


def chart_or_hole(c, u, v):
    """The charts have first rank at most u or second rank at most v."""
    sites = ranks(c)
    if (u+1, 0) not in sites or (0, v+1) not in sites:
        return None
    holes = [(i, j) for i in range(1, u+2) for j in range(1, v+2)
             if (i, j) not in sites and (i-1, j) in sites and (i, j-1) in sites]
    return min(holes, key=lambda p: (sum(p), p[0]))


@cache
def factors(c, h):
    pair, = hole_split(c, *h)
    return pair


def check(m, n, u, v):
    bound = u+v
    incidences = Counter()
    requests = set()
    checked = 0
    for c in cells((m, n)) - {()}:
        if (u+1, v+1) in ranks(c):
            continue
        h = chart_or_hole(c, u, v)
        if h is None:
            continue
        parts = factors(c, h)
        assert all(ranks(p) < ranks(c) for p in parts)
        first = sum(h)-1
        for j in range(first, len(c)-1):
            for sign in range(2):
                z = truncate(c, j, sign)
                assert factors(z, h) == tuple(truncate(p, j, sign) for p in parts)
                preferred = chart_or_hole(z, u, v)
                if preferred == h:
                    continue
                assert j <= max(first, u, v) and j <= bound
                if j == bound:
                    assert h == (u+1, v) and preferred == (u, v+1)
                    assert {(u-1, v+1), (u, v), (u+1, v-1)} <= ranks(z)
                requests.add((z, h))
                incidences[j] += 1
        checked += 1

    distinct = Counter(len(z)-1 for z, _ in requests)
    upper = Counter((max(i for i, _ in ranks(z)), max(j for _, j in ranks(z)))
                    for z, _ in requests if len(z)-1 == bound)
    print(f'D^{m} tensor D^{n}, strips ({u},{v}): {checked} crossing cells')
    print('Different face choices by degree (incidences, distinct):',
          [(d, incidences[d], distinct[d]) for d in sorted(distinct)])
    print('Highest-degree requests by pair of projection ranks:', dict(sorted(upper.items())))
    highest = {z for z, _ in requests if len(z)-1 == bound}
    representatives = set()
    face_cells = cache(cells)
    for z in highest:
        maxima = tuple(max(p[axis] for p in ranks(z)) for axis in range(2))

        def face_coordinates(label):
            return tuple((rank, 2) if rank == maximum else (rank, tag)
                         for (rank, tag), maximum in zip(label, maxima))

        rep = row_map(z, 0, face_coordinates)
        assert rep in face_cells(maxima)
        representatives.add(rep)
    print(f'{len(representatives)} highest-degree requests in their minimal face globes')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('m', 'n', 'u', 'v'):
        parser.add_argument(name, type=int)
    args = parser.parse_args()
    if min(args.m, args.n, args.u, args.v) < 1:
        parser.error('all dimensions and strip widths must be positive')
    check(args.m, args.n, args.u, args.v)
