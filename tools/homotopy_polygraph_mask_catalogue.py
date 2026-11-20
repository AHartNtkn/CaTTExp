"""Enumerate exact zero-mask axis types for excursion-free semaphore graphs."""

from collections import deque
from itertools import combinations, product

from homotopy_polygraph_parking import acquisition_before_release
from homotopy_polygraph_semaphore import Ring, clock_chart, histories
from homotopy_polygraph_two_resources import profiles


def extend(signature, mask):
    # Keep one edge for a constant run of positive length.
    if len(signature) >= 2 and signature[-2:] == (mask, mask):
        return signature
    return signature + (mask,)


def catalogue(vertices, edges, resources):
    if any(acquisition_before_release(edges, ('P', r), ('V', r)) for r in range(resources)):
        raise ValueError("an individual resource admits an excursion")
    outgoing = {v: [] for v in vertices}
    for a, action, b in edges:
        outgoing[a].append((action, b))

    result = set()
    # Each resource either always holds, starts free, or needs a last release.
    for initial in product(range(3), repeat=resources):
        free = sum(1 << r for r, role in enumerate(initial) if role == 1)
        pending = sum(1 << r for r, role in enumerate(initial) if role == 2)
        queue = deque((v, free, pending, (free,)) for v in outgoing)
        seen = set(queue)
        while queue:
            v, free, pending, signature = queue.popleft()
            if not pending:
                result.add(signature)
            for action, w in outgoing[v]:
                next_masks = [(free, pending)]
                if action is not None:
                    op, r = action
                    bit = 1 << r
                    if op == 'P':
                        if pending & bit:
                            continue
                        next_masks = [(free & ~bit, pending)]
                    elif op == 'V':
                        if free & bit:
                            continue
                        if pending & bit:
                            next_masks.append((free | bit, pending & ~bit))
                    else:
                        raise ValueError(f'unknown operation {op}')
                for f, p in next_masks:
                    item = (w, f, p, extend(signature, f))
                    if item not in seen:
                        seen.add(item)
                        queue.append(item)
    return result


def bounded_catalogue(vertices, edges, resources, length):
    """Independent literal count enumeration for short controls."""
    found = set()
    outgoing = {v: [] for v in vertices}
    for a, action, b in edges:
        outgoing[a].append((action, b))

    def visit(v, word):
        releases = [word.count(('V', r)) for r in range(resources)]
        # A resource either reaches zero or stays positive for the whole word.
        for extra in product(range(2), repeat=resources):
            initial = tuple(x + y for x, y in zip(releases, extra))
            row, = profiles([word], [initial])
            sig = ()
            for counts in row:
                sig = extend(sig, sum(1 << r for r in range(resources) if not counts[r]))
            found.add(sig)
        if len(word) < length:
            for action, w in outgoing[v]:
                visit(w, word + (action,))
    for start in vertices:
        visit(start, ())
    return found


def mask_grid(axes, resources):
    legal = set()
    for pos in product(*(range(len(row)) for row in axes)):
        enabled = [i for i, t in enumerate(pos) if t + 1 < len(axes[i])]
        for n in range(len(enabled) + 1):
            for moving in combinations(enabled, n):
                mask = 0
                for i, (row, t) in enumerate(zip(axes, pos)):
                    mask |= row[t] & row[t + (i in moving)]
                if mask == (1 << resources) - 1:
                    legal.add((pos, moving))
    return legal


def check():
    # The release loop and the acquisition loop can each execute arbitrarily often.
    vertices = range(3)
    edges = [(0, ('V', 0), 0), (0, ('V', 1), 1), (1, None, 1),
             (1, ('P', 2), 2), (2, ('P', 0), 2)]
    possible = catalogue(vertices, edges, 3)
    short = bounded_catalogue(vertices, edges, 3, 3)
    assert short < possible
    assert bounded_catalogue(vertices, edges, 3, 8) == possible
    print(f'Cyclic three-resource graph: {len(possible)} axis types; '
          f'{len(possible - short)} first need more than three instructions.')

    programs = [(('P', r), None, None, ('V', 1 - r)) if i == 0
                else (('P', r), ('V', 1 - r)) for i, r in enumerate((0, 0, 1, 1))]
    states = profiles(programs, [(0, 1), (0, 1), (1, 0), (1, 0)])
    axes = [tuple(sum(1 << r for r in (0, 1) if not counts[r]) for counts in row)
            for row in states]
    short_axes = []
    for i, row in enumerate(axes):
        sig = ()
        for mask in row:
            sig = extend(sig, mask)
        word = programs[i]
        assert sig in catalogue(range(len(word) + 1),
                                [(j, op, j + 1) for j, op in enumerate(word)], 2)
        short_axes.append(sig)
    actual = mask_grid(axes, 2)
    layout = Ring(4)
    for pos in product(*(range(len(row)) for row in axes)):
        for flags in product(*(range(1 + int(t + 1 < len(row))) for t, row in zip(pos, axes))):
            moving = tuple(i for i, flag in enumerate(flags) if flag)
            assert clock_chart(layout, programs, states, pos, moving, 2) == ((pos, moving) in actual)
    reduced = mask_grid(short_axes, 2)
    raw_betti = histories(programs, actual)
    reduced_betti = histories([row[1:] for row in short_axes], reduced)
    for betti in (raw_betti, reduced_betti):
        assert betti[:2] == (1, 1) and not any(betti[2:])
    print(f'Subdivision check: {len(actual)} spatial cubes and {len(reduced)} compressed cubes.')


if __name__ == '__main__':
    check()
