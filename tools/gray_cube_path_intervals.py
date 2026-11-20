"""Verify the supports, ranks and one-sided wedge reductions at fixed cube paths."""
from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, permutations, product

from gray_full_support_cuts import support
from gray_globe_comparison import boundary, globe, strict_cells
from gray_globe_section import trim


@cache
def word(chain):
    # A path from the initial vertex has one edge at each successive vertex weight.
    ordered = sorted(chain, key=lambda g: sum(entry == (0, 1) for entry in g))
    return tuple(next(i for i, (d, _) in enumerate(g) if d) for g in ordered)


def inversions(path):
    return frozenset((b, a) for i, a in enumerate(path) for b in path[i+1:] if b < a)


def precedence(u, v):
    return frozenset((a, b) for i, a in enumerate(u) for b in u[i+1:] if v.index(a) < v.index(b))


def allowed(g, relations):
    # When b has started or is moving, every predecessor a must already be done.
    return all(g[b] == (0, 0) or g[a] == (0, 1) for a, b in relations)


def delta(chain):
    result = Counter()
    for g, n in chain.items():
        for h, coefficient in boundary(g).items():
            result[h] += n*coefficient
    return result


def check_columns(cell, spectators):
    """Arrival at the final vertex of I and departure along any initial edge of the spoke cube."""
    n = len(cell[0][0][0])
    zero, one, edge = (0, 0), (0, 1), (1, 2)
    seam = (one,) + (zero,)*(n-spectators-1)
    previous = None
    for d, pair in enumerate(cell[1:]):
        splits = []
        for chain in pair:
            columns = [Counter(), Counter(), Counter()]
            arrival, departure = Counter(), Counter()
            for g in chain:
                w = g[spectators:]
                if w == seam:
                    columns[1][g] += 1
                elif w[0] != one:
                    assert all(z == zero for z in w[1:])
                    columns[0][g] += 1
                else:
                    columns[2][g] += 1
                marked = g[:spectators] + seam
                if w == (edge,) + seam[1:]:
                    arrival[marked] += 1
                if w[0] == one and w[1:].count(edge) == 1 and w[1:].count(one) == 0:
                    departure[marked] += 1
            assert sum(columns, Counter()) == Counter(chain)
            ends = [Counter(cell[0][0]) if d == 0 else Counter(), arrival, departure,
                    Counter(cell[0][1]) if d == 0 else Counter()]
            if d == 0:
                assert sum(arrival.values()) == sum(departure.values()) == 1
            for j, column in enumerate(columns):
                rhs = Counter()
                if previous is not None:
                    rhs.update(previous[1][j])
                    rhs.subtract(previous[0][j])
                for side in (0, 1):
                    for g, n_ in ends[j+side].items():
                        rhs[g] += (-1)**d*(2*side-1)*n_
                assert delta(column) == rhs
            splits.append(columns)
        previous = splits


def check_supports(n):
    extent = tuple((((0, v),)*n,) for v in (0, 1))
    shapes = list(product(globe(1), repeat=n))
    unions, heights = defaultdict(set), defaultdict(int)
    columns_checked = 0
    for padded in strict_cells((1,)*n, n):
        if padded[0] != extent:
            continue
        cell = trim(padded)
        poles = tuple(word(row) for row in cell[1])
        unions[poles].update(support(cell))
        heights[poles] = max(heights[poles], len(cell)-1)
        # I^(n-3) on the left, then x followed by two independent spokes.
        spatial = n-3
        if all(allowed(g, ((spatial, n-2), (spatial, n-1))) for g in support(cell)):
            check_columns(cell, spatial)
            columns_checked += 1
    paths = list(permutations(range(n)))
    inv = {p: inversions(p) for p in paths}
    assert unions.keys() == {(u, v) for u in paths for v in paths if inv[v] <= inv[u]}
    for (u, v), observed in unions.items():
        relations = precedence(u, v)
        predicted = {g for g in shapes if allowed(g, relations)}
        assert predicted == observed
        assert heights[u, v] == max(sum(d for d, _ in g) for g in predicted)
    print(f'{n}-cube: all {len(unions)} comparable extreme path pairs have exactly the predicted '
          f'support unions and ranks; {columns_checked} cubical wedge factorizations checked.')


def six_cube():
    n = 6
    paths = list(permutations(range(n)))
    inv = {p: inversions(p) for p in paths}
    totals = Counter()
    stars = set()
    all_pairs = set(combinations(range(n), 2))
    for u in paths:
        for v in paths:
            if not inv[v] <= inv[u]:
                continue
            same = all_pairs - (inv[u] - inv[v])
            if not same:
                totals['full'] += 1
                continue
            centers = set.intersection(*(set(ab) for ab in same))
            if not centers:
                totals['rank at most four'] += 1
                continue
            center = min(centers)
            group = set.union(*(set(ab) for ab in same))
            assert group == set(range(min(group), max(group)+1))
            ordered = precedence(u, v)
            assert all(a == center for a, _ in ordered) or all(b == center for _, b in ordered)
            side = 'one side' if min(group) == 0 or max(group) == n-1 else 'both sides'
            key = len(same), side
            totals[key] += 1
            stars.add((center, ordered))
    # Check the actual face sets, including all inactive-coordinate labels, for each star.
    for center, ordered in stars:
        spokes = {b if a == center else a for a, b in ordered}
        before = all(a == center for a, _ in ordered)
        fixed = (0, int(not before))
        for g in product(globe(1), repeat=n):
            on_arm = all(g[i] == fixed for i in spokes)
            on_large_cube = g[center] == (0, int(before))
            assert allowed(g, ordered) == (on_arm or on_large_cube)
    unresolved = totals['full'] + sum(count for key, count in totals.items()
                                       if isinstance(key, tuple) and (key[0] == 1 or key[1] == 'both sides'))
    assert sum(totals.values()) == 31711 and unresolved == 31
    print(f'Six-cube extreme intervals: {dict(totals)}; {unresolved} residual path pairs.')


if __name__ == '__main__':
    for dimension in (3, 4, 5):
        check_supports(dimension)
    six_cube()
