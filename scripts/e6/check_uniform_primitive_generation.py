"""Check the degree-four prism and cube boundary transports on finite arities."""

from collections import defaultdict
from itertools import product

import interchange_four_slot_ground as grid
import interchange_sorting_fiber as sorting
import interchange_two_moving as prism
from interchange_reachability import Presentation, solve, verify
from interchange_two_moving import reachable


def updates(history):
    return ''.join(event for event in history if event in 'XY')


def grid_face(history, source):
    # The signed Gray face records each update at one extreme of the
    # stationary word. Crossings of the other row may be interleaved.
    return all((history.index(cross) < i) == source
               for i, event in enumerate(history) if event in 'XY'
               for cross in ('pq' if event == 'X' else 'rs'))


def check_grid():
    histories = grid.raw_histories()
    forward, backward = defaultdict(set), defaultdict(set)
    for history in histories:
        for move in grid.primitive_moves(history):
            first = set(history[move.lo:move.mid])
            second = set(history[move.mid:move.hi])
            if move.kind == 'i':
                if not ((first <= set('XY') and second <= set('pqrs')) or
                        (first <= set('pqrs') and second <= set('XY'))):
                    continue
            elif move.hi - move.mid != 1:
                continue
            grid.verify_faces(history, move)
            start, end = grid.hist(history), grid.hist(move.target(history))
            assert updates(start) == updates(end)
            forward[start].add(end)
            backward[end].add(start)

    counts = []
    for source in (True, False):
        faces = {grid.hist(h) for h in histories if grid_face(h, source)}
        assert faces
        for order in {updates(h) for h in faces}:
            block = order + 'pqrs'
            connected = reachable(block, backward if source else forward)
            assert {h for h in faces if updates(h) == order} <= connected
        counts.append(len(faces))
    print(f'Left prism (2,2): {counts[0]} source classes, {counts[1]} target classes.')


def check_cube(columns):
    start = ''.join(reversed(columns))
    color = {slot: i for i, column in enumerate(columns) for slot in column}
    histories = sorting.raw_histories(start)

    def pair(event):
        return tuple(color[slot] for slot in event)

    forward, backward = defaultdict(set), defaultdict(set)
    for history in histories:
        for move in sorting.moves(start, history):
            if move.family == 'K15':
                # A true outer cut must separate entire factor colors.
                if max(color[x] for x in move.right) >= min(color[x] for x in move.left):
                    continue
            elif move.family == 'i':
                if len(move.left_events) != 1 or len(move.right_events) != 1:
                    continue
                if pair(move.left_events[0]) == pair(move.right_events[0]):
                    continue
            else:
                continue
            forward[history].add(move.target)
            backward[move.target].add(history)

    counts = []
    for source in (True, False):
        # A signed Gray face restricts on every individual triple to the
        # corresponding three-crossing order.
        faces = {h for h in histories if all(
            (h.index(y + z) < h.index(x + z) < h.index(x + y)) if source else
            (h.index(x + y) < h.index(x + z) < h.index(y + z))
            for x, y, z in product(*columns))}
        canonical = {h for h in faces if list(map(pair, h)) == sorted(map(pair, h), reverse=source)}
        assert canonical
        # Any particular representative of the three consecutive blocks works.
        for block in canonical:
            assert faces <= reachable(block, backward if source else forward)
        counts.append(len(faces))
    print(f'Cube {tuple(map(len, columns))}: {counts[0]} raw sources, {counts[1]} raw targets.')


def check_stationary_edge():
    start, end = 'abYX', 'XYab'
    cross = prism.Move('r', 0, 2, 4)
    routes = ((prism.Move('i', 2, 3, 4), cross),
              (cross, prism.Move('i', 0, 1, 2)))
    paths = []
    for route in routes:
        history = start
        contracted = [updates(history)]
        for move in route:
            assert move in prism.moves(history)
            prism.verify_move(history, move)
            history = move.target(history)
            if updates(history) != contracted[-1]:
                contracted.append(updates(history))
        assert history == end and contracted == ['YX', 'XY']
        paths.append(prism.walk(start, route))

    ground, _ = prism.ground(start, end)
    equations = Presentation(ground.vertices, ground.edges,
                             (r for r in ground.rules.values() if r.equation))
    equality = solve(equations, *paths)
    assert not equality.reachable and verify(equations, *paths, equality)
    print(f'Stationary edge: two routes specialize to the bare swap, '
          f'{len(equality.visited)} paths in the first equation class.')


if __name__ == '__main__':
    check_grid()
    for columns in (('ab', 'cd', 'e'), ('ab', 'c', 'de'), ('a', 'bc', 'de')):
        check_cube(columns)
    check_stationary_edge()
