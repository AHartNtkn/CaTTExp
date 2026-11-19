"""Degree-five reachability in the Response 12 completion on the Response 16 grid.

With a stationary right outer branch, the cut-zero auxiliaries specialize
to identities or already present operations. The proper cut-one join has
two independent positive 4-path inputs. Include their *whole* paths.
"""
from functools import cache

from interchange_four_slot_ground import check_mixed_examples, ground_all, primitive_moves, raw_histories, walk
from interchange_four_slot_rectangles import certify, rectangle_queries, window_paths
from interchange_reachability import Presentation, Rule, solve, verify
from interchange_two_moving import histories as one_partner_histories, moves as one_partner_moves


def shifted_joins(raw, moves_at):
    for crossing in moves_at(raw):
        if crossing.kind != 'i':
            continue
        # Before this inner crossing the spatially right operand is first
        # in time. Its spatially left partner moves forward by that width.
        lo, mid, hi = crossing.lo, crossing.mid, crossing.hi
        right_paths = window_paths(raw, lo, mid, moves_at)
        if not right_paths:
            continue
        for left in window_paths(raw, mid, hi, moves_at):
            transported = tuple(move.shift(lo - mid) for move in left)
            for right in right_paths:
                yield right + (crossing,) + transported, left + right + (crossing,)


@cache
def ground_completion(m, n):
    base = ground_all(m, n)
    extra = {}
    for raw in raw_histories(m, n):
        for lhs, rhs in shifted_joins(raw, primitive_moves):
            source, target = walk(raw, lhs), walk(raw, rhs)
            name = f'shifted_join {source.edges} {target.edges}'
            extra[name] = Rule(name, source, target)
    return Presentation(base.vertices, base.edges, [*base.rules.values(), *extra.values()])


def check_new_join(completed, join):
    base = ground_all(1, 1)
    for label, graph, source, target, reachable in (
        ('P forward', base, join.source, join.target, False),
        ('Response 12 forward', completed, join.source, join.target, True),
        ('Response 12 reverse', completed, join.target, join.source, False),
    ):
        certificate = solve(graph, source, target)
        assert certificate.reachable == reachable and verify(graph, source, target, certificate)
        if reachable:
            assert len(certificate.steps) == 1 and certificate.steps[0].rule == join.name
        result = 'one join step' if reachable else f'{len(certificate.visited)} paths in closed cut'
        print(f'Shifted join, {label}: {result}.')

    pairs = {(a, b) for a, b, _ in rectangle_queries(1, 1)}
    for source, target in pairs:
        previous = solve(base, target, source)
        assert not previous.reachable and verify(completed, target, source, previous)
        assert all(step.rule != join.name for path in previous.visited
                   for step, _ in completed.successors(path))
    print(f'The new join does not occur in any of the {len(pairs)} original reverse cuts.')


def check():
    # The three-slot alternative in the contraction proof uses Response 14.
    # Two disjoint positive 4-arguments would need at least four slots.
    assert not any(tuple(shifted_joins(raw, one_partner_moves)) for raw in one_partner_histories(2, 2))
    for arity, pairs in (((2, 0), 208), ((1, 1), 420), ((0, 2), 180)):
        completed = ground_completion(*arity)
        joins = [rule for rule in completed.rules.values() if rule.name.startswith('shifted_join ')]
        assert len(joins) == int(arity == (1, 1))
        print(f'{arity} has {len(joins)} proper shifted join rules.')
        counts = certify(*arity, presentation=completed)
        assert counts['distinct boundary pairs'] == pairs
        if joins:
            check_new_join(completed, joins[0])
    check_mixed_examples(ground_completion(1, 1))


if __name__ == '__main__':
    check()
