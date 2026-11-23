"""Finite part of the end-piece obstruction for upper unary contractions.

Use the equation overapproximation on the full reversal interval. For a
specified final letter g, every label in a path P g lies in its past, or
is g. Close that set under both inclusions supplied by each equation.
A label outside the result cannot occur in any spelling of P g. Run the
dual test for initial letters, allowing arbitrary following paths.
"""

from collections import defaultdict
from functools import cache
from itertools import product

from check_interchange_grid_contractions import normal_path
from interchange_triangle_join_interval import (
    ground_interval, raw_histories, restrict_interval,
)
from interchange_unary_runs import Cylinder, UnaryRuns
from t_endomorphisms import all_extensions, expansions


def check_interval(start):
    histories = set(raw_histories(start))
    classes, moves = restrict_interval(
        start, histories, histories, histories, lambda edge: True
    )
    graph, labels = ground_interval(classes, moves)
    equations = [(set(rule.source.edges), set(rule.target.edges))
                 for rule in graph.rules.values() if rule.equation]
    tests = []
    for boundary, other in [('source', 'target'), ('target', 'source')]:
        incident = defaultdict(set)
        for name, edge in graph.edges.items():
            incident[getattr(edge, boundary)].add(name)

        @cache
        def allowed(name):
            reached = set()
            pending = [getattr(graph.edges[name], other)]
            while pending:
                new = incident[pending.pop()] - reached
                reached.update(new)
                pending.extend(getattr(graph.edges[n], other) for n in new)
            reached.add(name)
            while True:
                size = len(reached)
                for lhs, rhs in equations:
                    if lhs <= reached:
                        reached.update(rhs)
                    if rhs <= reached:
                        reached.update(lhs)
                if len(reached) == size:
                    return reached

        for kind, fresh in [('r', start[0]), ('t', start[-1])]:
            pure = defaultdict(set)
            for edge, name in labels.items():
                if fresh not in edge.left + edge.right:
                    history = getattr(edge, boundary)
                    events = frozenset(history[edge.lo:edge.hi])
                    pure[classes[history]].add((name, events))

            count = 0
            for edge, name in labels.items():
                stationary, moving = ((edge.left, edge.right_events) if kind == 'r'
                                      else (edge.right, edge.left_events))
                if edge.family != kind or stationary != fresh:
                    continue
                for old, events in pure[classes[getattr(edge, boundary)]]:
                    if events.issubset(moving):
                        assert old not in allowed(name), (boundary, edge, old)
                        count += 1
            tests.append(count)
    return len(histories), len(graph.edges), tests


def check_two_letter_family(n):
    # Read actual rank-four boundaries of the three rank-five steps of each
    # site. v is the preceding r(w,b); right/left are pure lanes for X.
    def site(i, layer, target=False):
        lane = ('left', layer) if target else ('right', layer)
        middle = (lane, 'v') if target else ('v', lane)
        return (('left', 2),) * i + middle + (('right', 0),) * (n - 1 - i)

    def path(steps):
        assert all(a[2] == b[1] for a, b in zip(steps, steps[1:]))
        return tuple(steps)

    def step(i, name, a, b):
        return ((i, name), a, b)

    sites = []
    for i in range(n):
        left = step(i, 'L1', site(i, 0), site(i, 1))
        center = step(i, 'E1', site(i, 1), site(i, 1, True))
        right = step(i, 'T2', site(i, 1, True), site(i, 2, True))
        sites.append(path([left, center, right]))

    middle = path(sum(sites, ()))
    first, second = [], []
    for i, (left, center, right) in enumerate(sites):
        pre, post = middle[:3*i], middle[3*i+3:]
        e0 = step(i, 'E0', site(i, 0), site(i, 0, True))
        t1 = step(i, 'T1', site(i, 0, True), site(i, 1, True))
        l2 = step(i, 'L2', site(i, 1), site(i, 2))
        e2 = step(i, 'E2', site(i, 2), site(i, 2, True))
        path(pre + (e0, t1, right) + post)
        path(pre + (left, l2, e2) + post)
        assert pre + (left, center, right) + post == middle
        # Use a common tag here: the prefix tests themselves detect a mismatch.
        first.append(Cylinder('E', 0, 1, pre, ('z1',), (right,) + post,
                              (left,), (t1,)))
        second.append(Cylinder('E', 1, 2, pre + (left,), ('z2',), post,
                               (l2,), (right,)))
    solver = UnaryRuns(lambda x, y: x + y, lambda x, y: x == y)
    for i, j in product(range(n), repeat=2):
        assert (solver.merge(first[i], second[j]) is not None) == (i == j)
    return n*n


def check_interval_formula(rows, cols):
    """Compare the cut formula on each input with local block contraction."""
    results = set()
    histories = all_extensions(tuple(range(rows)), tuple(range(cols)))
    for word in histories:
        roots = {}
        cuts = set(range(len(word) + 1))
        for i in range(len(word)):
            for j in range(i + 1, len(word) + 1):
                piece = word[i:j]
                left = tuple(sorted({a for a, b in piece}))
                right = tuple(sorted({b for a, b in piece}))
                if len(left) * len(right) == len(piece) and piece in expansions(left, right):
                    roots[i, j] = (left, right)
                    cuts.difference_update(range(i + 1, j))
        boundaries = sorted(cuts)
        data = tuple(roots[i, j] for i, j in zip(boundaries, boundaries[1:]))
        assert data == normal_path(word)
        results.add(data)
    return len(histories), len(results)


if __name__ == '__main__':
    for n, expected in [(2, (1, 0, [0]*4)), (3, (2, 2, [0]*4)),
                        (4, (16, 53, [2]*4)), (5, (768, 3872, [419, 369, 369, 419]))]:
        result = check_interval('abcde'[:n][::-1])
        assert result == expected
        print(n, *result)
    for shape, expected in [((3, 2), (5, 2)), ((3, 3), (42, 21)), ((3, 4), (462, 272))]:
        result = check_interval_formula(*shape)
        assert result == expected
        print(f'{shape}: {result[0]} schedules, {result[1]} interval normal forms')
    print(sum(check_two_letter_family(n) for n in range(1, 17)),
          'composable two-letter tests')
