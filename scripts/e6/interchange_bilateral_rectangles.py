"""Verify temporal rectangles with two retained unary advances on a 2 x 2 shuffle.

For advances in opposite outer branches the saved integer ranks decide every
temporal rectangle in arbitrary path contexts. For two right advances we
enumerate the split-crossing cases, then certify the full loop intervals.
"""
from argparse import ArgumentParser
from itertools import combinations_with_replacement

from interchange_bilateral_ground import ground_all, hist, primitive_moves, raw_histories, walk
from interchange_four_slot_loop_half import interval_edges
from interchange_four_slot_rectangles import factorized_inputs
from interchange_reachability import Path, solve, verify
from interchange_regular_rectangles import Rank, find_rank, verify_rank
from interchange_two_moving import Move


# Each entry is the integer score of one edge, in sorted edge-name order.
SCORES = {
    'XZ': (
        -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1,
        0, -2, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, -1,
        0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 6, 5,
        0, 0, 1, 1, 1, 1, 0, 2, 2, 5, 0, -5, 0, 3, 3, 0, 0, 1, 0, 0, 1, -1,
        0, 0, -4, 1, 0, 1, 0, 1, 0, 1, 5, 4, 0, -1, 0, 0, 0, 3, 3, 2, 0, 4,
        0, -1, 4, -1, -3, 0, 0, -3, 0, 1, 0, 2, 3, 0, 0, -1, 0, -6, -1, 0, -2, 0,
        0, 0, 0, 4, 1, 6, -1, 0, 0, 0, 6, 5, 0, 0, 0, 4, 0, 2, 2, 2, 1, 4,
        0, 0, -2, 0, 0, 5, 4, 0, 4, 3, 3, 1, 1, 0, 0, 0, -1, 0, 2, 2, 1, 0,
        0, -3, 0, -5, 0, 2, 1, 0, 2, 3, 0, 6, -2, -1, 0, 0, 0,
    ),
    'XW': (
        1, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, -3, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 5, 5, 0, 0, 0, 0, 3, 0, 0, 0,
        0, 0, 0, 1, 1, 0, 0, 0, 0, 3, 1, 0, 0, 1, 0, 0, 0, 3, 0, -9, 0, 0,
        -2, 0, -2, 4, 0, 1, -2, 0, 0, 0, 1, 3, -9, 3, 0, 0, -5, -11, -2, -5, 0, 2,
        -1, 0, 1, 0, 0, 5, 0, 0, 7, 0, 9, 2, 0, 0, 0, 4, 0, 2, 4, 0, 4, -4,
        0, 0, -4, 2, 0, 0, 0, -4, -9, 0, 0, 0, -7, 0, 4, -5, 0, 0, 0, 0, 0, 3,
        0, 0, 0, -3, 5, 0, 0, -4, 0, 0, 4, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0,
        3, -11, 0, 0, 0, -5, 0, 0, -15, -4, 0, 0, -2, 0, 0, 4, 0, 0, 5, 4, 0, 0,
        3, 5, 5, -5, 1, -1, -6, 0, 0, 0, -7, 0, 5, 0, 0,
    ),
    'YZ': (
        -2, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, 0, 0, -4, 2, 4,
        3, 0, -8, -8, 1, 0, 0, 0, 0, 3, 3, -9, 0, 0, 0, 0, 0, 4, -4, 0, -4, 2,
        -2, 0, 0, 4, -4, 0, -2, 6, 0, -2, -4, 4, 2, 4, -6, -2, -2, -4, 6, 6, -6, -4,
        -2, 0, 0, -2, 0, 0, 6, 0, -6, 0, 0, 1, 0, 6, 0, 0, 13, 7, 0, 0, 6, 0,
        0, 2, 0, 0, -7, 2, 2, -8, 0, -2, -10, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0,
        0, 0, 9, 9, 0, 0, 0, 0, -7, 0, 0, 9, -9, 0, 0, 0, 0, 0, 0, 9, 0, 0,
        7, 7, 0, 0, 9, 0, 0, 0, 0, -5, 0, 2, 0, 4, 0, 0, 0, 0, 0, -11, -4, 0,
        0, 0, 4, 0, 0, 7, 2, -5, 0, 0, -11, -11, 0, 0, 2,
    ),
    'YW': (
        -2, 0, 0, 0, 6, 0, -4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0,
        0, 0, 0, -2, 0, 0, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0,
        0, 0, 0, 0, 0, 0, -4, 0, 0, 0, -6, -6, -6, 0, -2, 0, -4, -2, 0, -2, -6, -6,
        -1, -6, 0, 0, 0, 0, -8, -2, -8, -8, 0, 0, 0, -2, 5, -1, -4, -6, -2, 1, -2, -4,
        0, 7, -2, 7, 0, -6, -2, -2, 1, -4, -6, 3, 2, 2, -4, 4, 0, -8, -4, 0, 0, 0,
        -8, -4, -15, -11, 0, 0, -6, 0, 0, 0, -9, 0, -6, 1, -1, -1, -1, 0, 0, 0, -1, -8,
        0, 0, 0, 0, 7, 8, 0, 0, -8, 0, 0, -4, -12, 0, 0, 0, 1, 1, 3, -7, 1, 1,
        0, 0, -8, -1, -1, 1, 0, -1, -7, 0, -8, 0, 0, -11, 8, 0, 1,
    ),
}


def certify_rank(pair, graph, synthesize):
    deltas = [(rule.source, rule.target) for rule in graph.rules.values()
              if rule.name.startswith('delta ')]
    index = {e: i for i, e in enumerate(sorted(graph.edges))}
    scores = SCORES[pair]
    assert len(scores) == len(index) and deltas
    rank = Rank({}, index, dict(enumerate(scores)))
    assert verify_rank(graph, deltas, rank)
    drops = [rank.evaluate(a)[1] - rank.evaluate(b)[1] for a, b in deltas]
    print(f'{pair}: {len(deltas)} strict exchanges, score drops {min(drops)} to {max(drops)}.')
    if synthesize:
        fresh = find_rank(graph, deltas)
        assert fresh is not None and verify_rank(graph, deltas, fresh)


def check_split(pair, graph):
    mixed, cuts = set(), {}
    placements = 0
    for raw, a, b, c, d in factorized_inputs(raw_histories(*pair), primitive_moves):
        placements += 1
        source, target = walk(raw, c + d + a + b), walk(raw, c + a + d + b)
        key = source, target
        if any(m.kind != 'i' for m in a) and any(m.kind != 'i' for m in d):
            mixed.add(key)
        if key not in cuts:
            forward = solve(graph, source, target)
            reverse = solve(graph, target, source)
            assert forward.reachable and verify(graph, source, target, forward)
            assert not reverse.reachable and verify(graph, target, source, reverse)
            cuts[key] = len(reverse.visited)
    print(f'{pair}: {placements} placements, {len(cuts)} distinct pairs, {len(mixed)} '
          f'mixed-active pairs, largest reverse cut {max(cuts.values())}.')


def check_right_loop(graph, crossings_first):
    # The two unaries can form a proper crossing-free window only on distinct
    # slots. The sole possible inner exchange there is WZ -> ZW.
    raw = 'prqsWZ' if crossings_first else 'WZprqs'
    loop = Move('i', 1, 2, 3) if crossings_first else Move('i', 3, 4, 5)
    swap = Move('i', 4, 5, 6) if crossings_first else Move('i', 0, 1, 2)
    finish = swap.target(raw)
    before, = walk(raw, (loop,)).edges
    after, = walk(finish, (loop,)).edges
    exchange, = walk(raw, (swap,)).edges
    vertices, edges = interval_edges(graph, hist(raw), hist(finish))
    assert vertices == {hist(raw), hist(finish)} and edges == {before, after, exchange}
    before_swap = Path(hist(raw), (before, exchange))
    after_swap = Path(hist(raw), (exchange, after))
    steps = set()
    for rule in graph.rules.values():
        directions = [(rule.source, rule.target)]
        if rule.equation:
            directions.append((rule.target, rule.source))
        for lhs, rhs in directions:
            if lhs.start in vertices and set(lhs.edges) <= edges:
                assert set(rhs.edges) <= edges
                steps.add((rule.name.split()[0], lhs, rhs))
    lhs, rhs = (after_swap, before_swap) if crossings_first else (before_swap, after_swap)
    assert steps == {('delta', lhs, rhs)}
    print(f'{raw}: two vertices, three edges, one directed loop/exchange rule.')


def check_mixed_example():
    # All four inputs proper, with opposite mixed active edges. The reverse
    # cut contains an actual use of the binary join factorization.
    graph = ground_all('Y', 'W')
    raw = 'WpqrsY'
    a, b = Move('t', 0, 1, 2), Move('i', 1, 2, 3)
    c, d = Move('r', 4, 5, 6), Move('r', 3, 4, 5)
    source, target = walk(raw, (c, d, a, b)), walk(raw, (c, a, d, b))
    forward, reverse = solve(graph, source, target), solve(graph, target, source)
    assert forward.reachable and verify(graph, source, target, forward)
    assert not reverse.reachable and verify(graph, target, source, reverse)
    assert any(step.rule.startswith('binary_join_factorization ') and other in reverse.visited
               for path in reverse.visited for step, other in graph.successors(path))
    print(f'Wpq|rsY: {len(forward.steps)} forward step, {len(reverse.visited)} paths '
          'in the reverse cut, including binary join factorization.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--synthesize', action='store_true')
    args = parser.parse_args()
    for letters in combinations_with_replacement('XYZW', 2):
        pair = ''.join(letters)
        graph = ground_all(*letters)
        if pair in SCORES:
            certify_rank(pair, graph, args.synthesize)
        check_split(pair, graph)
        if pair == 'ZW':
            for crossings_first in (True, False):
                check_right_loop(graph, crossings_first)
    check_mixed_example()
