"""Certify the unbounded loop intervals with all four crossings in one half.

Compute the complete directed 4-graph interval inside the Response 12
grounding before inspecting 5-rules. The three-edge shape and the only
rewrite determine reachability at every loop multiplicity.
"""
from collections import defaultdict

from interchange_four_slot_ground import hist, verify_faces, walk
from interchange_reachability import Path, solve, verify
from interchange_response12_rectangles import ground_completion
from interchange_two_moving import Move, reachable


def interval_edges(graph, start, finish):
    outgoing, incoming = defaultdict(set), defaultdict(set)
    for edge in graph.edges.values():
        outgoing[edge.source].add(edge.target)
        incoming[edge.target].add(edge.source)
    vertices = reachable(start, outgoing) & reachable(finish, incoming)
    return vertices, {name for name, e in graph.edges.items()
                      if e.source in vertices and e.target in vertices}


def check(crossings_first):
    graph = ground_completion(1, 1)
    # The rq -> qr move is an endomorphism by K15 on the *whole* block.
    start_raw, finish_raw = ('prqsYX', 'prqsXY') if crossings_first else ('YXprqs', 'XYprqs')
    start, finish = hist(start_raw), hist(finish_raw)
    loop = Move('i', 1, 2, 3) if crossings_first else Move('i', 3, 4, 5)
    unary = Move('i', 4, 5, 6) if crossings_first else Move('i', 0, 1, 2)
    for raw, move in ((start_raw, loop), (finish_raw, loop), (start_raw, unary)):
        verify_faces(raw, move)
    before, = walk(start_raw, (loop,)).edges
    after, = walk(finish_raw, (loop,)).edges
    exchange, = walk(start_raw, (unary,)).edges
    vertices, edges = interval_edges(graph, start, finish)
    assert vertices == {start, finish} and edges == {before, after, exchange}
    for name, source, target in ((before, start, start), (after, finish, finish),
                                 (exchange, start, finish)):
        e = graph.edges[name]
        assert (e.source, e.target, e.weight) == (source, target, 1)

    def route(n, j):
        return Path(start, (before,) * j + (exchange,) + (after,) * (n-j))

    applicable = []
    for rule in graph.rules.values():
        # Also check potential reverse applications of each 4-equation.
        orientations = [(rule.source, rule.target)]
        if rule.equation:
            orientations.append((rule.target, rule.source))
        for lhs, rhs in orientations:
            if lhs.start in vertices and set(lhs.edges) <= edges:
                assert rhs.start in vertices and set(rhs.edges) <= edges
                applicable.append((rule.name.split()[0], lhs, rhs))
    j0, j1 = (0, 1) if crossings_first else (1, 0)
    assert applicable == [('delta', route(1, j0), route(1, j1))]

    # Replay finite examples in the full presentation; the interval and rule
    # checks above, which never enumerate loop words, give the unbounded proof.
    comparisons = 0
    for n in range(13):
        for j in range(n + 1):
            for k in range(n + 1):
                a, b = route(n, j), route(n, k)
                certificate = solve(graph, a, b)
                assert certificate.reachable == (j <= k if crossings_first else j >= k)
                assert verify(graph, a, b, certificate)
                comparisons += 1
    print(f'{start} -> {finish}: {len(vertices)} vertices, {len(edges)} edges, '
          f'one directed delta (j {j0} -> {j1}); {comparisons} boundary pairs verified.')


def check_four_positive_inputs():
    # Early A,B move two successive X's ahead of Y. Late C moves a
    # third X ahead of the full crossing, after which D performs H twice.
    graph = ground_completion(3, 1)
    start = 'YXXprqsX'
    moves = {'A': Move('i', 0, 1, 2), 'B': Move('i', 1, 2, 3),
             'C': Move('r', 3, 7, 8), 'H': Move('i', 5, 6, 7)}

    def path(schedule):
        raw = start
        edges = []
        for label in schedule:
            if label == 'H':
                # Re-expose the inner rq exchange after the previous loop.
                raw = raw.replace('pqrs', 'prqs')
            move = moves[label]
            verify_faces(raw, move)
            edges.extend(walk(raw, (move,)).edges)
            raw = move.target(raw)
        return Path(hist(start), tuple(edges))

    source, target = path('CHHAB'), path('CAHHB')
    assert graph.end(source) == graph.end(target) == 'XXYXpqrs'
    forward, reverse = solve(graph, source, target), solve(graph, target, source)
    assert forward.reachable and verify(graph, source, target, forward)
    assert not reverse.reachable and verify(graph, target, source, reverse)
    print(f'Four positive inputs with D = H²: {len(forward.steps)} forward steps, '
          f'{len(reverse.visited)} paths in the reverse cut.')


if __name__ == '__main__':
    check(crossings_first=True)
    check(crossings_first=False)
    check_four_positive_inputs()
