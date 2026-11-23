"""Check stationary graph blocks and the contraction at a published insertion."""
from collections import Counter
from itertools import combinations, permutations, product

from semistrict_surface_configuration_blocks import Graph, block, subsets
from semistrict_surface_scalar_pairs import check_splices


def inflate(outer, name, inner):
    """Substitute a graph for a vertex of an ordered complete graph."""
    levels = {(i, j): level for i, j, level in outer.levels}
    internal = {(i, j): level for i, j, level in inner.levels}
    order = tuple(y for x in outer.order for y in (inner.order if x == name else (x,)))
    result = []
    for i, j in combinations(sorted(order), 2):
        if (i, j) in internal:
            level = internal[i, j]
        else:
            edge = tuple(sorted(name if v in inner.order else v for v in (i, j)))
            level = levels[edge]
        result.append((i, j, level))
    return Graph(order, tuple(result))


def stationary_data(g, slots):
    root = min(slots)
    inner = g.restrict(slots)
    outer = g.restrict(set(g.order) - (slots - {root}))
    return (outer, inner) if inflate(outer, root, inner) == g else None


def check_unions():
    counts = Counter()
    names = frozenset(range(4))
    possible = [s for s in subsets(names) if 1 < len(s) < len(names)]
    edges = list(combinations(sorted(names), 2))
    for order in permutations(sorted(names)):
        for levels in product(range(2), repeat=len(edges)):
            graph = Graph(order, tuple((*e, l) for e, l in zip(edges, levels, strict=True)))
            # Compare whole moving families, including motion of an external
            # edge or a change of order. Equal restrictions test stationarity.
            moves = [Graph(order, tuple((i, j, level ^ (ix == k))
                                        for ix, (i, j, level) in enumerate(graph.levels)))
                     for k in range(len(edges))]
            moves += [Graph(order[:k] + (order[k+1], order[k]) + order[k+2:], graph.levels)
                      for k in range(len(order)-1)]
            possible_here = {s: d for s in possible if (d := stationary_data(graph, s))}
            for other in [graph] + moves:
                frozen = {}
                for s, (outer, inner) in possible_here.items():
                    d = stationary_data(other, s)
                    if d and d[1] == inner:
                        frozen[s] = (outer, d[0])
                for s, t in combinations(frozen, 2):
                    if s & t:
                        union = s | t
                        low = stationary_data(graph, union)
                        high = stationary_data(other, union)
                        assert low and high and low[1] == high[1]
                        counts['overlapping or nested stationary blocks'] += 1
                        for first in (s, t):
                            quotient_union = (union - first) | {min(first)}
                            a, b = frozen[first]
                            qa, qb = stationary_data(a, quotient_union), stationary_data(b, quotient_union)
                            assert qa and qb and qa[1] == qb[1]
                            counts['quotient factorizations'] += 1
                    else:
                        a, b = frozen[s]
                        qa, qb = stationary_data(a, t), stationary_data(b, t)
                        assert qa and qb and qa[1] == qb[1]
                        counts['disjoint stationary blocks'] += 1
    # Move an entire three-point interval through an outside point. Its two
    # overlapping stationary two-point intervals persist during this motion.
    for order in permutations(range(4)):
        i, j, k, exterior = order
        inside = Graph(order[:3], tuple((*e, 0) for e in combinations(sorted(order[:3]), 2)))
        root = min(inside.order)
        pair = tuple(sorted((root, exterior)))
        before = inflate(Graph((root, exterior), ((*pair, 0),)), root, inside)
        after = inflate(Graph((exterior, root), ((*pair, 1),)), root, inside)
        assert below(before, after)
        for keep in ((i, j), (j, k), (i, j, k)):
            a, x = stationary_data(before, frozenset(keep))
            b, y = stationary_data(after, frozenset(keep))
            assert x == y and a != b and below(a, b)
        counts['moving prisms with proper overlapping blocks'] += 1
    return counts


def contract(g, groups, gaps):
    # Restore the prescribed exterior levels while keeping all internal edges.
    if len(groups) == 1:
        return g.restrict(groups[0])
    split = min(range(len(gaps)), key=gaps.__getitem__)
    return block(contract(g, groups[:split+1], gaps[:split]),
                 contract(g, groups[split+1:], gaps[split+1:]), gaps[split])


def below(x, y):
    positions = {e: k for k, e in enumerate(x.order)}
    changed = {e: k for k, e in enumerate(y.order)}
    for (i, j, a), (_, _, b) in zip(x.levels, y.levels, strict=True):
        if a > b or (a == b and (positions[i] < positions[j]) != (changed[i] < changed[j])):
            return False
    return True


def check_refinements():
    counts = Counter()
    # Three original scalar slots; replace the middle one with a standard
    # composite of two slots, retaining the two outer divergences.
    names = (0, 1, 3)
    for outer_order in permutations(names):
        for outer_levels in product(range(3), repeat=3):
            g = Graph(outer_order, tuple((*e, l) for e, l in
                                        zip(combinations(names, 2), outer_levels, strict=True)))
            for left, inside, right in product(range(3), repeat=3):
                # The new divergence with the outside must still be that of
                # the original slot (the trunk condition for this splice).
                if inside < max(left, right):
                    continue
                coarse_start = contract(g, ((0,), (1,), (3,)), (left, right))
                if not below(coarse_start, g):
                    continue
                for inner_order in ((1, 2), (2, 1)):
                    inner = Graph(inner_order, ((1, 2, inside),))
                    refined = inflate(g, 1, inner)
                    coarse = contract(refined, ((0,), inner_order, (3,)), (left, right))
                    fine = contract(refined, ((0,), (inner_order[0],), (inner_order[1],), (3,)),
                                    (left, inside, right))
                    assert coarse == fine == inflate(coarse_start, 1, inner)
                    assert below(coarse, refined)
                    for keep in subsets(refined.order):
                        groups = [(0,), (inner_order[0],), (inner_order[1],), (3,)]
                        retained = [tuple(i for i in group if i in keep) for group in groups]
                        assert contract(refined.restrict(keep), retained, (left, inside, right)) == fine.restrict(keep)
                        counts['contractions with empty slots'] += 1
                    counts['coarse and refined contractions'] += 1
    return counts


if __name__ == '__main__':
    print('Signed slot pairs at actual tree insertions:', check_splices())
    for check in (check_unions, check_refinements):
        for label, total in check().items():
            print(f'{label}: {total}')
