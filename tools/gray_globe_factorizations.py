"""Classify every binary cut of a globe-pair tableau by its occupied rank pairs."""
import argparse
from collections import Counter, defaultdict
from itertools import product

from gray_crossing_paths import coordinates
from gray_globe_comparison import atom, boundary, face
from gray_globe_section import EMPTY_ROW, cells, trim
from gray_path_wedge import compose


def rank(g):
    return g[0][0], g[1][0]


def profile(c):
    result = set()
    for negative, positive in c:
        ranks = [rank(g) for g in negative]
        assert len(set(ranks)) == len(ranks)
        assert sorted(ranks) == sorted(rank(g) for g in positive)
        result.update(ranks)
    assert all((not i or (i-1, j) in result) and (not j or (i, j-1) in result)
               for i, j in result)
    return result


def components(ranks, cut):
    remaining = {g for g in ranks if sum(g) > cut}
    groups = []
    while remaining:
        group = set()
        stack = [remaining.pop()]
        while stack:
            i, j = stack.pop()
            group.add((i, j))
            for adjacent in ((i-1, j), (i+1, j), (i, j-1), (i, j+1)):
                if adjacent in remaining:
                    remaining.remove(adjacent)
                    stack.append(adjacent)
        groups.append(group)
    return sorted(groups, key=lambda g: min(i for i, j in g if i+j == cut+1))


def orders(c, cut, owner):
    """At a shared cut coordinate identify the first of the two directed edges."""
    start = {rank(g): g for g in c[cut][0]}
    precedences = set()
    for side, chain in enumerate(c[cut+1]):
        edges = defaultdict(list)
        for g in chain:
            for h, coefficient in boundary(g).items():
                if coefficient < 0:
                    edges[rank(h)].append((owner[rank(g)], h))
        signed = set()
        for coordinate, sources in edges.items():
            if len(sources) == 2 and sources[0][0] != sources[1][0]:
                first, second = sources
                if second[1] == start[coordinate]:
                    first, second = second, first
                assert first[1] == start[coordinate] and second[1] != start[coordinate]
                signed.add((first[0], second[0]))
        if side == 0:
            precedences = signed
        assert signed == precedences
    return precedences


def factorizations(c, ranks, cut):
    blocks = components(ranks, cut)
    owner = {coord: index for index, block in enumerate(blocks) for coord in block}
    precedences = orders(c, cut, owner)
    result = set()
    for mask in product((False, True), repeat=len(blocks)):
        if any(mask[after] and not mask[before] for before, after in precedences):
            continue
        middle = Counter(c[cut][0])
        for g in c[cut+1][0]:
            if mask[owner[rank(g)]]:
                middle.update(boundary(g))
        assert min(middle.values()) >= 0
        at_cut = tuple(sorted(middle.elements()))
        left = list(c[:cut]) + [(c[cut][0], at_cut)]
        right = list(c[:cut]) + [(at_cut, c[cut][1])]
        for row in c[cut+1:]:
            for side, rows in ((True, left), (False, right)):
                rows.append(tuple(tuple(g for g in chain if mask[owner[rank(g)]] == side)
                                  for chain in row))
        result.add((trim(left), trim(right)))
    return result


def hole_split(c, i, j):
    """The separated rank regions compose in exactly one order."""
    k = i+j-2
    for a, b in factorizations(c, profile(c), k):
        upper_a = [r for r in profile(a) if sum(r) > k]
        upper_b = [r for r in profile(b) if sum(r) > k]
        if not upper_a or not upper_b:
            continue
        if ((all(p >= i for p, q in upper_a) and all(q >= j for p, q in upper_b))
                or (all(q >= j for p, q in upper_a) and all(p >= i for p, q in upper_b))):
            yield a, b


def check_crossing(c, ranks):
    if (1, 2) not in ranks:
        hole, name = (1, 2), 'fixed second coordinate'
    elif (2, 1) not in ranks:
        hole, name = (2, 1), 'fixed first coordinate'
    elif (2, 2) not in ranks:
        hole, name = (2, 2), 'fixed traversal order'
    else:
        return 'mixed middle tensor'
    w = coordinates(c)[2]
    (start,), (end,) = w[0]
    if hole[0]+hole[1] == 3:
        axis = 1 if hole == (1, 2) else 0
        assert start[axis] == end[axis]
    else:
        assert all(start[d] != end[d] for d in range(2))
        # Both signed paths traverse the coordinates in the same order.
        def first_axis(chain):
            first, = (basis for basis in chain if atom(basis)[0][0] == (start,))
            return int(first[0][0] == 0)
        assert first_axis(w[1][0]) == first_axis(w[1][1])

    (x, y), = hole_split(c, *hole)
    if hole == (2, 2):
        assert x[:2] == y[:2] == c[:2]
        assert all((1, 2) not in profile(t) or (2, 1) not in profile(t) for t in (x, y))
    else:
        # Each factor belongs to an edge-times-globe tile.
        for t in (x, y):
            assert any(max(rank_pair[axis] for rank_pair in profile(t)) <= 1
                       for axis in range(2))
    k = sum(hole)-2
    if len(c)-1 > k+1:
        for side in (0, 1):
            cut = len(c)-2
            expected = tuple(t if len(t) <= cut+1 else trim(face(t, side)) for t in (x, y))
            assert list(hole_split(face(c, side), *hole)) == [expected]
    return name


def check(m, n):
    all_cells = cells((m, n)) - {()}
    profiles = {c: profile(c) for c in all_cells}
    for c, ranks in profiles.items():
        corners = [(i, j) for i, j in ranks
                   if (i+1, j) not in ranks and (i, j+1) not in ranks]
        if len(corners) == 1:
            assert len(c[-1][0]) == 1 and c == atom(c[-1][0][0])

    if min(m, n) >= 2:
        poles = atom(((m, 2), (n, 2)))[:2]
        sectors = Counter(check_crossing(c, ranks) for c, ranks in profiles.items() if c[:2] == poles)
        print('Crossing hom:', dict(sorted(sectors.items())))

    cuts = pairs = 0
    for k in range(m+n):
        targets = [c for c in all_cells if len(c) > k+1]
        by_source = defaultdict(list)
        actual = defaultdict(set)
        for c in targets:
            by_source[c[:k], c[k][0]].append(c)
            # The two identity factors at this cut.
            for side in (0, 1):
                chain = c[k][side]
                face = c[:k] + ((chain, chain),)
                actual[c].add((face, c) if side == 0 else (c, face))
        for x in targets:
            for y in by_source[x[:k], x[k][1]]:
                height = max(len(x), len(y))
                xy = compose(x + (EMPTY_ROW,)*(height-len(x)), y + (EMPTY_ROW,)*(height-len(y)), k)
                assert xy in profiles
                actual[xy].add((x, y))
        for c in targets:
            predicted = factorizations(c, profiles[c], k)
            assert predicted == actual[c], (k, c)
            cuts += 1
            pairs += len(predicted)
    print(f'D^{m} tensor D^{n}: {len(all_cells)} cells, {cuts} cell/cut pairs, '
          f'{pairs} binary factorizations')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    args = parser.parse_args()
    if min(args.m, args.n) < 0:
        parser.error('globe dimensions must be nonnegative')
    check(args.m, args.n)
