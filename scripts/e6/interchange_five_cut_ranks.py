"""All proper temporal rectangles in the pure five-strand sorting interval.

A cut is the intermediate permutation of the five named strands. It fixes the
early crossing set E. Every triangle on either original route uses three early
or three late crossings. A return preserves the Gray 4-chain, so all its
4-path representatives use only such triangles. Its endpoints have histories
through the cut. Take the union of directed intervals between ALL such
histories in the monochromatic-triangle graph, including both directions of
K15. This retains every eligible route with any choice of inactive paths,
even when intermediate 3-histories fail to visit the cut.

ground_interval supplies the encompassing equation and directed-rule system
on this union. Each actual elementary cut delta has simultaneous raw
representatives in the two disjoint temporal windows. Enumerate these at all
cuts, including composite operands and all spatial and temporal padding. A
cut delta swaps a late primitive 4-occurrence with an early one. The two
transported occurrences keep their own operands, and their common endpoint
is the concatenation of the new early and late histories.

For each cut find_rank searches for a conserved edge charge and a scalar
rank consisting of a linear edge sum and a skew bilinear sum on ordered pairs
of edges. verify_rank checks all charges, rules and strict deltas exactly.
Charge conservation cancels every cross term with an arbitrary 4-path
prefix or suffix. Pasting the elementary deltas therefore proves strictness
for every pair of nonidentity active paths, with arbitrary inactive paths
and no limit on the number of loops. Completing either end of a shorter
pure sorting interval by fixed temporal 3-whiskers embeds any return in
the full reversal. Stationary padding likewise covers fewer than five slots.

Run with Python 3 and glpsol on PATH.
"""

from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, product
from math import lcm

from interchange_reachability import Path
from interchange_regular_rectangles import Rank, find_rank, verify_rank
from interchange_sorting_fiber import moves, raw_histories, states
from interchange_triangle_join_interval import (
    START, gray, ground_interval, operand, restrict_interval,
)


def cut_histories(raws):
    seeds = defaultdict(set)
    early_sets = {}
    for history in raws:
        for time, cut in enumerate(states(START, history)):
            early = frozenset(history[:time])
            assert early == early_sets.setdefault(cut, early)
            seeds[cut].add(history)
    return seeds, early_sets


def elementary_pairs(seeds, time):
    for history in seeds:
        positive = [move for move in moves(START, history) if move.family != 'K15']
        early = [move for move in positive if move.hi <= time]
        late = [move for move in positive if move.lo >= time]
        yield from product(early, late)


def cut_graph(raws, seeds, early):
    @cache
    def monochromatic(triangle):
        return len({a + b in early for a, b in combinations(triangle, 2)}) == 1

    def allowed(move):
        return move.family == 'K15' or all(monochromatic(t) for t in gray(move))

    classes, at = restrict_interval(START, seeds, seeds, raws, allowed)
    graph, labels = ground_interval(classes, at)
    return classes, at, graph, labels


def projected_deltas(pairs, time, classes, at, labels):
    def transport(move, after, end):
        copies = {labels[e] for e in at[after] if e.target == end and
                  (e.lo, e.hi, operand(e)) == (move.lo, move.hi, operand(move))}
        only, = copies
        return only

    result = set()
    for early, late in pairs:
        end = early.target[:time] + late.target[time:]
        source = Path(classes[early.source], (labels[late], transport(early, late.target, end)))
        target = Path(source.start, (labels[early], transport(late, early.target, end)))
        result.add((source, target))
    return result


def integer_rank(rank):
    # Clearing the two denominators separately multiplies the entire scalar
    # score by the same positive factor, including its quadratic terms.
    q = lcm(*(v.denominator for row in rank.charges.values() for v in row.values()))
    s = lcm(*(v.denominator for v in rank.coefficients.values()))
    charges = {edge: {i: int(v * q) for i, v in row.items()} for edge, row in rank.charges.items()}
    coeff = {k: int(v * s) * (1 if isinstance(k, tuple) else q*q)
             for k, v in rank.coefficients.items()}
    return Rank(charges, rank.index, coeff)


def check():
    raws = set(raw_histories(START))
    seeds, early_sets = cut_histories(raws)
    assert len(raws) == 768 and len(seeds) == 120
    assert sum(map(len, seeds.values())) == 8448
    raw_counts = Counter()
    active_cuts = comparisons = quadratic_cuts = max_seeds = max_histories = 0
    for cut in sorted(seeds):
        early = early_sets[cut]
        pairs = list(elementary_pairs(seeds[cut], len(early)))
        if not pairs:
            continue
        raw_counts.update((a.family, d.family) for a, d in pairs)
        classes, at, graph, labels = cut_graph(raws, seeds[cut], early)
        deltas = projected_deltas(pairs, len(early), classes, at, labels)
        directed = {(r.source, r.target) for r in graph.rules.values()
                    if r.name.startswith('delta ') and not r.equation}
        assert deltas <= directed
        rank = find_rank(graph, sorted(deltas))
        assert rank is not None, cut
        assert verify_rank(graph, deltas, integer_rank(rank)), cut
        active_cuts += 1
        comparisons += len(deltas)
        quadratic_cuts += bool(rank.charges)
        max_seeds = max(max_seeds, len(seeds[cut]))
        max_histories = max(max_histories, len(classes))

    assert (active_cuts, comparisons, max_seeds, max_histories) == (86, 10976, 112, 138)
    assert raw_counts == {('i', 'i'): 16424, **{p: 2250 for p in product('i', 'rt')},
                          **{p: 2250 for p in product('rt', 'i')},
                          **{p: 502 for p in product('rt', repeat=2)}}
    print(f'Verified all {comparisons} cut-labelled deltas on {active_cuts} active five-strand cuts.')
    print(f'{sum(raw_counts.values())} raw occurrences, including {raw_counts["i", "i"]} inner/inner.')
    print(f'{quadratic_cuts} cuts used ordered-pair scores. Largest active cut had {max_seeds} '
          f'compatible histories. Largest restricted interval contained {max_histories}.')


if __name__ == '__main__':
    check()
