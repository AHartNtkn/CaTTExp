"""Ground the all-mixed shuffle interval on a moving slot and stationary slots.

The moving slot x has sum(sizes) consecutive unary 3-advances. In the
2-word z_k ... z_1 x, cross x with z_1,...,z_k, in this order. A history
is a word in c (next crossing) and u (next advance). The fixed 3-endpoints
are (c u^m_1)...(c u^m_k) and (u^m_1 c)...(u^m_k c).

Every 3-event touches x. An outer block crossing in a 3-equation has
only one possible event order, and an inner 4-exchange would need
disjoint positive histories. A triple atom would cross two passive
slots. No input 4-globe exists. A proper join also needs disjoint
histories. Consequently the only primitive 4-move is r moving a unary
run left of a crossing run. Every pair in its Cartesian product changes
order irreversibly. Between our endpoints only pairs in the same
designated block can change order. Thus a surviving r uses a single
crossing and a consecutive run of advances of its block. Its varying
composition equation expands it uniquely; stationary-context laws
transport the same expansion. Every 4-equation consequently preserves
the word of block labels. Every shuffle of those labels is realized.

A proper inner naturality requires two disjoint positive histories.
An outer higher naturality needs a positive 4-cell in one operand:
that cell already uses x and some z_i, and an independent positive
stationary slot must cross z_i as well as x. A binary W needs two
disjoint positive histories, and there is no input 5-globe. Thus the
only degree-five steps are temporal exchanges and their contexts.
They exchange disjoint time intervals, moving the earlier one forward.
Two occurrences from the same block cannot have disjoint windows:
both traverse the same crossing. Composite exchanges factor into unit
exchanges of differing block indices. Each adjacent decreasing pair
of indices admits that exchange. Reachability is exactly inclusion of
inversion sets for occurrences labelled by their index within a block.
Indeed bubble the first desired occurrence to the front. Every occurrence
it passes must be larger, since the desired word has no new inversion.
Iterate on the remaining suffix.

For arbitrary 3-endpoints in the same 2-interval, choose the temporal
cut of a four-input rectangle. Every advance/crossing pair exchanged
in a 4-path is wholly early or wholly late: the endpoints already agree
on the relative order of every cross-cut pair, and a swap is irreversible.
The Cartesian product changed by an r is therefore unicolored. Read its
color width*height times. All splits preserve this word, even when the
two decompositions of a 2x2 tile are equated. Every intermediate history
still has its full early segment before its late segment, by the same
pair-order argument and the fixed internal orders of advances and of
crossings. In a contextual exchange, an earlier window cannot contain a
late occurrence if the later window contains an early one. Thus the
number of late-before-early pairs cannot increase. It drops strictly
between CDAB and CADB whenever A and D are proper.
"""

import sys
from collections import defaultdict
from itertools import combinations, product
from math import comb, factorial, prod

from interchange_path_grading import History, r_faces, word
from interchange_reachability import Edge, Path, Presentation, Rule, query_cli, solve, verify


def histories(crossings, advances):
    for positions in combinations(range(crossings + advances), crossings):
        chosen = set(positions)
        yield ''.join('c' if i in chosen else 'u' for i in range(crossings + advances))


def events(history):
    index = 0
    for event in history:
        if event == 'c':
            index += 1
            yield (index, 'x')
        else:
            yield ('x',)


def moves(history):
    """Every concrete r on this 2-interval, including composite operands."""
    cross_count = history.count('c')
    initial = word((*range(cross_count, 0, -1), 'x'))
    for middle in range(1, len(history)):
        for first in range(middle - 1, -1, -1):
            if history[first] != 'c':
                break
            for last in range(middle + 1, len(history) + 1):
                if history[last - 1] != 'u':
                    break
                prefix = History(initial, tuple(events(history[:first])))
                state = prefix.end
                pos = next(i for i, (name, _) in enumerate(state) if name == 'x')
                width, height = middle - first, last - middle
                varying = History((state[pos],), (('x',),) * height)
                source, target = r_faces(varying, state[pos-width:pos])
                source = prefix.then(source.pad(state[:pos-width], state[pos+1:]))
                target = prefix.then(target.pad(state[:pos-width], state[pos+1:]))
                after = history[:first] + 'u' * height + 'c' * width + history[last:]
                assert source.events == tuple(events(history[:last]))
                assert target.events == tuple(events(after[:last]))
                yield after, history[:first].count('c'), width, height


def closure(edges, start):
    seen = {start}
    pending = [start]
    while pending:
        for vertex in edges[pending.pop()]:
            if vertex not in seen:
                seen.add(vertex)
                pending.append(vertex)
    return seen


def route(start, labels, elementary):
    sequence = []
    state = start
    for label in labels:
        name, state = elementary[state, label]
        sequence.append(name)
    return Path(start, tuple(sequence))


def ground_history_pair(start, finish):
    """Present every 4-equation and elementary 5-exchange on the star interval."""
    if (set(start + finish) - {'c', 'u'} or sorted(start) != sorted(finish)):
        raise ValueError('both histories must have the same crossings and advances')
    vertices = list(histories(start.count('c'), start.count('u')))
    forward = {v: set() for v in vertices}
    backward = {v: set() for v in vertices}
    all_moves = []
    for before in vertices:
        for after, block, width, height in moves(before):
            forward[before].add(after)
            backward[after].add(before)
            all_moves.append((before, after, block, width, height))
    interval = closure(forward, start) & closure(backward, finish)
    if finish not in interval:
        raise ValueError('there is no 4-path between the specified 3-histories')
    edges = {}
    tiles = {}
    elementary = {}
    for before, after, block, width, height in all_moves:
        if before in interval and after in interval:
            name = f'{before}/{block}:{width}x{height}'
            edges[name] = Edge(before, after, width * height)
            tiles[before, block, width, height] = name
            if width == height == 1:
                elementary[before, block] = name, after

    rules = []
    for (before, block, width, height), name in tiles.items():
        # (10) splitting the unary run uses the initial advances first.
        # (12) splitting the crossing run uses the last crossings first.
        splits = [
            ((block, width, cut), (block, width, height - cut))
            for cut in range(1, height)
        ] + [
            ((block + cut, width - cut, height), (block, cut, height))
            for cut in range(1, width)
        ]
        for first, second in splits:
            part = tiles[(before, *first)]
            rest = tiles[(edges[part].target, *second)]
            rules.append(Rule(
                f'split {name} at {first}', Path(before, (name,)), Path(before, (part, rest)), True
            ))
    for before in sorted(interval):
        enabled = [i for i in range(start.count('c')) if (before, i) in elementary]
        for early, late in combinations(enabled, 2):
            rules.append(Rule(
                f'exchange {early},{late} at {before}',
                route(before, (late, early), elementary),
                route(before, (early, late), elementary),
            ))
    return Presentation(tuple(sorted(interval)), edges, rules), elementary


def ground_interval(sizes):
    start = ''.join('c' + 'u' * size for size in sizes)
    finish = ''.join('u' * size + 'c' for size in sizes)
    presentation, elementary = ground_history_pair(start, finish)
    expected = {
        ''.join('u' * i + 'c' + 'u' * (size - i) for i, size in zip(indices, sizes))
        for indices in product(*(range(size + 1) for size in sizes))
    }
    assert presentation.vertices == expected
    return presentation, start, elementary


def shuffles(sizes, prefix=()):
    if not any(sizes):
        yield prefix
    for label, count in enumerate(sizes):
        if count:
            remaining = list(sizes)
            remaining[label] -= 1
            yield from shuffles(remaining, prefix + (label,))


def inversions(labels):
    earlier = []
    seen = {}
    result = set()
    for label in labels:
        item = label, seen.get(label, 0)
        seen[label] = item[1] + 1
        result.update((old, item) for old in earlier if old[0] > label)
        earlier.append(item)
    return result


def check(sizes):
    presentation, start, elementary = ground_interval(sizes)
    schedules = list(shuffles(sizes))
    assert len(schedules) == factorial(sum(sizes)) // prod(factorial(m) for m in sizes)
    graph = {s: set() for s in schedules}
    for s in schedules:
        for i in range(len(s) - 1):
            if s[i] > s[i+1]:
                graph[s].add(s[:i] + (s[i+1], s[i]) + s[i+2:])
    orders = {s: inversions(s) for s in schedules}
    related = 0
    for s in schedules:
        reachable = closure(graph, s)
        assert reachable == {t for t in schedules if orders[t] <= orders[s]}
        related += len(reachable)
        # Saturate every unexpanded r-tiling using the grounded path rules.
        ground_paths = {route(start, s, elementary)}
        pending = list(ground_paths)
        while pending:
            for _, other in presentation.successors(pending.pop()):
                if other not in ground_paths:
                    ground_paths.add(other)
                    pending.append(other)
        assert reachable == {t for t in schedules if route(start, t, elementary) in ground_paths}
    if sizes == (2, 2):
        for s in schedules:
            for t in schedules:
                source, target = route(start, s, elementary), route(start, t, elementary)
                actual = solve(presentation, source, target)
                assert verify(presentation, source, target, actual)
                assert actual.reachable == (orders[t] <= orders[s])
        assert related == 20
    print(f'{sizes}: {comb(sum(sizes)+len(sizes), len(sizes))} 3-histories; '
          f'{len(presentation.vertices)} in interval; '
          f'{len(schedules)} 4-classes; {related} reachable ordered pairs (including identities).')


def check_two_squares():
    # Each side of the time cut contains a full 2x2 tile. Its two atomic
    # expansions differ at the internal exchange and are equal by (10),(12).
    start = 'ccuuccuu'
    presentation, elementary = ground_history_pair(start, 'uuccuucc')
    early = ((1, 0, 1, 0), (1, 1, 0, 0))
    late = tuple(tuple(i + 2 for i in labels) for labels in early)
    equations = Presentation(presentation.vertices, presentation.edges,
                             [r for r in presentation.rules.values() if r.equation])
    for labels in early:
        atomized = route(start, labels, elementary)
        tile, = (name for name, edge in presentation.edges.items()
                 if edge.source == start and edge.target == presentation.end(atomized))
        for source, target in ((atomized, Path(start, (tile,))), (Path(start, (tile,)), atomized)):
            expansion = solve(equations, source, target)
            assert expansion.reachable and verify(equations, source, target, expansion)
    a, b, c, d = (1, 0), (1, 0), (3, 2), (3, 2)
    source = route(start, c + d + a + b, elementary)
    target = route(start, c + a + d + b, elementary)
    positive = solve(presentation, source, target)
    negative = solve(presentation, target, source)
    assert positive.reachable and not negative.reachable
    assert verify(presentation, source, target, positive)
    assert verify(presentation, target, source, negative)
    # Equation components identify every raw 4-path. Doing the remaining
    # reachability computation on classes includes arbitrary interleavings
    # of equations and directed rules, also in either inactive context.
    outgoing = defaultdict(list)
    for name, edge in presentation.edges.items():
        outgoing[edge.source].append((name, edge.target))
    paths = []
    pending = [(start, ())]
    while pending:
        state, history = pending.pop()
        if state == 'uuccuucc':
            paths.append(Path(start, history))
        pending.extend((after, history + (name,)) for name, after in outgoing[state])

    classes = {}
    for path in paths:
        if path in classes:
            continue
        representative = path
        classes[path] = representative
        pending = [path]
        while pending:
            for _, other in equations.successors(pending.pop()):
                if other not in classes:
                    classes[other] = representative
                    pending.append(other)
    assert set(classes) == set(paths)
    graph = {r: set() for r in classes.values()}
    for path in paths:
        graph[classes[path]].update(classes[other] for _, other in presentation.successors(path))
    reach = {r: closure(graph, r) for r in graph}
    assert all(a == b or a not in reach[b] for a in graph for b in reach[a])
    rectangles = set()
    for e, l, i, j in product(early, late, range(1, 4), range(1, 4)):
        before = classes[route(start, l + e, elementary)]
        after = classes[route(start, l[:j] + e[:i] + l[j:] + e[i:], elementary)]
        assert after in reach[before] and before not in reach[after]
        rectangles.add((before, after))
    pairs = sum(map(len, reach.values()))
    assert (len(paths), len(graph), pairs, len(rectangles)) == (1530, 262, 14378, 36)
    print(f'Two 2x2 tiles: {len(presentation.vertices)} histories, '
          f'{len(presentation.edges)} contextual 4-edges, {len(presentation.rules)} ground rules; '
          f'{len(paths)} raw paths, {len(graph)} classes, {pairs} reachable ordered pairs; '
          f'{len(rectangles)} proper four-input rectangles; '
          f'example certificate {len(positive.steps)} steps, reverse cut {len(negative.visited)} paths.')


def read_query(data):
    start, finish = data['histories']
    presentation, elementary = ground_history_pair(start, finish)

    def requested(labels):
        if not isinstance(labels, list) or any(type(i) is not int for i in labels):
            raise ValueError('a route is a list of zero-based crossing indices')
        try:
            path = route(start, labels, elementary)
        except KeyError as error:
            raise ValueError(f'no elementary move at {error.args[0]}') from error
        if presentation.end(path) != finish:
            raise ValueError('route ends at a different 3-history')
        return path

    return presentation, requested(data['source']), requested(data['target'])


if __name__ == '__main__':
    if len(sys.argv) > 1:
        query_cli(read_query, 'Decide reachability between two mixed routes in a moving-slot interval.')
    else:
        for example in ((2, 2), (3, 3), (2, 2, 2)):
            check(example)
        check_two_squares()
