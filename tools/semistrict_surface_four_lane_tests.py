"""Prescribed rank-three degree-six tests on the four-lane binary history.

--prescribed D gives the single D-by-D comparison for all four-lane cases.
Output is accepted by semistrict_surface_four_lane_cuts.py. The audit also
computes the rank of all pure-lane readings of the grid abelianization.
"""
from argparse import ArgumentParser
from itertools import combinations, count, islice, product
import json

from semistrict_surface_four_lane_cuts import append_power, contract, seed, solve
from semistrict_surface_spatial_antichain import bracket, inverse


def grid(d, word):
    return dict(events=[(0, 1)] * d + [(2, 3)] * d, word=word)


def pair(d, i, j, a, b, power=1):
    return dict(after=[*range(i), *range(d, d + j)], pair=[a, b], multiple=power)


def abelian_basis(d):
    names = []
    def register(name, i, j, left, right):
        word = [pair(d, i, j, a, b, x * y) for a, x in left for b, y in right]
        names.append((name, word))
    u = [(0, 1), (1, 1)]
    v = [(2, 1), (3, 1)]
    x = [(0, 1), (1, -1)]
    y = [(2, 1), (3, -1)]
    register('sum x sum', 0, 0, u, v)
    for i in range(d + 1):
        register(f'left within {i}', i, 0, [(0, 1)], [(1, 1)])
        register(f'left difference {i} x sum', i, 0, x, v)
        register(f'right within {i}', 0, i, [(2, 1)], [(3, 1)])
        register(f'sum x right difference {i}', 0, i, u, y)
    for i, j in product(range(d + 1), repeat=2):
        register(f'difference {i} x difference {j}', i, j, x, y)
    return names


def enumeration():
    # The first item exercises a commutator. Positive integer letter costs
    # then grade all finite signed words on the nonnegative quadrant.
    yield [(1, 0, 1), (0, 1, 1), (1, 0, -1), (0, 1, -1)]
    def words(cost):
        if cost == 0:
            yield []
        else:
            for k in range(1, cost + 1):
                for i, sign in product(range(k), (1, -1)):
                    for suffix in words(cost - k):
                        yield [(i, k - 1 - i, sign), *suffix]
    for cost in count(1):
        yield from words(cost)


def position(d, entry):
    i = sum(k < d for k in entry['after'])
    return i, len(entry['after']) - i


def prescribed(d):
    original = seed(d)
    root = original['word']
    corner = (0, d)
    height = peak = 0
    for entry in root:
        if position(d, entry) == corner:
            height += entry.get('multiple', 1)
            peak = max(peak, height)
    assert height == 0
    leaves, candidates = [], []
    for letters in islice(enumeration(), d):
        if any(i + 1 > d or j >= d for i, j, _ in letters):
            continue
        normal = []
        for i, j, sign in letters:
            append_power(normal, (i + 1, j), sign)
        if not normal:
            continue
        candidate = [pair(d, i + 1, j, 0, 2, sign) for i, j, sign in letters]
        tag = [pair(d, *corner, 0, 2, peak + 1 + len(leaves))]
        leaves.append(tag + candidate + inverse(tag))
        candidates.append(candidate)
    while len(leaves) > 1:
        leaves = [bracket(leaves[i], leaves[i + 1]) if i + 1 < len(leaves) else leaves[i]
                  for i in range(0, len(leaves), 2)]
    if leaves:
        root = bracket(root, leaves[0])
    return grid(d, root), candidates


def audit():
    for d in range(1, 4):
        basis = abelian_basis(d)
        pairs = list(combinations(range(4), 2))
        pivots = {}
        for mask in range(1 << (2 * d + 2)):
            rows = [[0] * len(basis) for _ in pairs]
            for t, (_, terms) in enumerate(basis):
                for entry in terms:
                    i, j = position(d, entry)
                    a, b = [v ^ ((mask >> (i if v < 2 else d + 1 + j)) & 1)
                            for v in entry['pair']]
                    row = rows[pairs.index(tuple(sorted((a, b))))]
                    row[t] += (1 if a < b else -1) * entry['multiple']
            # A full-rank minor modulo 101 also certifies rational injectivity.
            for row in rows:
                for k in sorted(pivots):
                    z = row[k]
                    if z:
                        row = [(a - z*b) % 101 for a, b in zip(row, pivots[k])]
                k = next((k for k, z in enumerate(row) if z % 101), None)
                if k is not None:
                    inv = pow(row[k], -1, 101)
                    pivots[k] = [a * inv % 101 for a in row]
        assert len(pivots) == len(basis) == 1 + 4*(d + 1) + (d + 1)**2
        print(f'Grid {d}: independent pure readings have rank {len(pivots)} '
              f'on the {len(basis)}-dimensional abelianization.')
    for d in range(1, 5):
        data, candidates = prescribed(d)
        def raw_zero(word):
            return solve(grid(d, word))['raw_fills']
        def retained(entry):
            i, j = position(d, entry)
            return (i, j) == (0, d) or (i > 0 and j < d)
        assert not raw_zero([v for v in data['word'] if retained(v)])
        for site in range(2 * d):
            assert solve(contract(data, site))['raw_fills']
        for w in candidates:
            # Retraction killing all vertices used by this specific leaf.
            lost = {position(d, v) for v in w}
            assert raw_zero([v for v in data['word'] if position(d, v) not in lost])
        print(f'Grid {d}: {len(candidates)} nontrivial shortlist entries, '
              f'{len(data["word"])} signed terms, every single contraction fills.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--prescribed', type=int)
    args = parser.parse_args()
    if args.prescribed is not None:
        print(json.dumps(prescribed(args.prescribed)[0]))
    else:
        audit()
