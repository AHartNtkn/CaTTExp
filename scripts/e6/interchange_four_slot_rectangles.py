"""Test all four-input temporal rectangles with a crossing on each side.

The inputs are built in the two separate temporal intervals. The solver
can use every grounded rule, including rules acting across that cut.
"""

from collections import Counter
from functools import cache

from interchange_four_slot_ground import ground_all, primitive_moves, raw_histories, walk
from interchange_reachability import solve, verify


@cache
def window_paths(raw, lo, hi, moves_at=primitive_moves):
    """Every nonempty path supported in [lo,hi), on the specified raw history."""
    # A crossing in the complementary window prevents a full K15 block here.
    # Detect a cycle explicitly before using finite path enumeration.
    paths = []
    todo = [(raw, (), frozenset({raw}))]
    while todo:
        state, path, seen = todo.pop()
        for move in moves_at(state):
            if lo <= move.lo and move.hi <= hi:
                target = move.target(state)
                if target in seen:
                    raise ValueError(f'cyclic proper subinterval: {raw}, {lo}, {hi}, {path}')
                extended = path + (move,)
                paths.append(extended)
                todo.append((target, extended, seen | {target}))
    return tuple(paths)


def is_mixed(moves):
    return any(m.kind == 'r' for m in moves)


def rectangle_queries(m, n):
    crossings = frozenset('pqrs')
    for raw in raw_histories(m, n):
        for cut in range(1, len(raw)):
            if crossings.isdisjoint(raw[:cut]) or crossings.isdisjoint(raw[cut:]):
                continue
            for early in window_paths(raw, 0, cut):
                for late in window_paths(raw, cut, len(raw)):
                    for i in range(1, len(early) + 1):
                        a, b = early[:i], early[i:]
                        for j in range(len(late)):
                            c, d = late[:j], late[j:]
                            source = walk(raw, c + d + a + b)
                            target = walk(raw, c + a + d + b)
                            yield source, target, is_mixed(b) and is_mixed(c)


def certify(m, n, presentation=None):
    if presentation is None:
        presentation = ground_all(m, n)
    counts = Counter()
    checked = {}
    for source, target, mixed_inactive in rectangle_queries(m, n):
        counts['rectangles'] += 1
        counts['both inactive mixed'] += mixed_inactive
        key = (source, target)
        if key in checked:
            continue
        forward = solve(presentation, source, target)
        if not forward.reachable or not verify(presentation, source, target, forward):
            raise ValueError(f'missing forward: {source} -> {target}')
        reverse = solve(presentation, target, source)
        if reverse.reachable or not verify(presentation, target, source, reverse):
            raise ValueError(f'failed reverse obstruction: {source} -> {target}: {reverse.steps}')
        checked[key] = len(reverse.visited)
    assert checked
    counts['distinct boundary pairs'] = len(checked)
    counts['largest reverse cut'] = max(checked.values())
    print(f'({m},{n})', dict(counts))
    return counts


if __name__ == '__main__':
    for arity, placements, pairs in (((2, 0), 230, 208), ((1, 1), 464, 420), ((0, 2), 202, 180)):
        counts = certify(*arity)
        assert (counts['rectangles'], counts['distinct boundary pairs']) == (placements, pairs)
