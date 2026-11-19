"""Check the continuation after an inversion-increasing shifted join on six strands.

The early triangle E is the spatially right input Y. The late triangle L
is the spatially left input X. In Y I X the product puts the complete L
history before the complete E history. On the 3-target of X both triangles
have their target braid order. The temporal context may sort bridges.

Contract the smallest of the three E strands. Each surviving late triangle
other than L would meet E on a nonminimal E strand x. The common-slot
inversion argument puts all such triangles before E on a proposed return:
x is smallest in the late triangle and nonminimal in E. It cannot be
stationary for both marks on the same side, and H_R cannot move this late
mark before E. Each late bridging triangle is in the inactive C, so its
late-before-early count is maximal at both rectangle boundaries.

The suffix following X can thus have only triangles using both surviving
E strands. Widen the search by admitting all triangles of that shape,
even when their bridge colors are incompatible. Use all spatial/temporal
windows of the five-strand grounder and both directions of K15.

Also check temporal exchanges with L in the earlier window and E later.
Pinning of every shared-slot pair in the enclosing 5-cycle puts every late
bridging triangle before E and every early bridging triangle after L. Test
the prefix and suffix separately, deleting each of the six strands in turn.
The inverted windows may include bridge events and can be wide. The search
allows every raw history at their common cut with the permitted incidences
and the two source (prefix test) or target (suffix test) braid orders.
"""

from collections import defaultdict
from itertools import combinations

from interchange_sorting_fiber import moves, raw_histories, states
from interchange_triangle_join_interval import gray


def crossing_order(group):
    """Target braid order for three letters; the single crossing for two."""
    return tuple(a + b for a, b in combinations(group, 2))


def continuation(early, trajectories, transitions):
    late = ''.join(x for x in 'abcde' if x not in early)
    before_operands = late[::-1] + early[::-1]
    cut = late[::-1] + early
    late_braid = crossing_order(late)
    join_face = late_braid + crossing_order(early)
    starts, targets = set(), set()
    for history, trajectory in trajectories.items():
        if before_operands in trajectory:
            lo = trajectory.index(before_operands)
            if history[lo:lo + len(join_face)] == join_face:
                starts.add(history)
        if cut in trajectory and tuple(e for e in history if e in late_braid) == late_braid:
            targets.add(history)
    assert starts and targets

    seen, pending = set(starts), list(starts)
    while pending:
        for target, triangles in transitions[pending.pop()]:
            if target not in seen and all(set(early) <= set(t) for t in triangles):
                seen.add(target)
                pending.append(target)
    assert seen.isdisjoint(targets), (early, seen & targets)
    return len(starts), len(seen), len(targets)


def in_braid_order(history, group, after):
    braid = crossing_order(group)
    expected = braid if after else braid[::-1]
    return tuple(e for e in history if e in braid) == expected


def respects_incidences(history, early_events):
    """On each strand every early crossing precedes every late crossing."""
    touched_late = set()
    for event in history:
        if event in early_events:
            if touched_late.intersection(event):
                return False
        else:
            touched_late.update(event)
    return True


def temporal_exclusion(early, early_left, after, trajectories, steps):
    late = ''.join(x for x in 'abcde' if x not in early)

    def blocks(e, l):
        return e + l if early_left else l + e

    designated = blocks(early, late[::-1])
    inverted = blocks(early[::-1], late)
    early_events = set(crossing_order(early))
    for x in early:
        for y in late:
            if (x < y) == early_left:
                early_events.add(''.join(sorted((x, y))))
    starts, targets = set(), set()
    for h, trajectory in trajectories.items():
        if not all(in_braid_order(h, group, after) for group in (early, late)):
            continue
        if designated in trajectory:
            targets.add(h)
        if inverted in trajectory and respects_incidences(h, early_events):
            starts.add(h)
    assert starts and targets
    seen, pending = set(starts), list(starts)
    # After both marked edges only early bridges can still change. Before
    # both only late bridges can already have changed. Gray-zero moves in
    # either region are unrestricted, and we allow all triples of the right
    # shape even when some of their actual bridge colors disagree.
    multiplicity = 2 if after else 1
    while pending:
        for h, triangles in steps[pending.pop()]:
            if h not in seen and all(sum(x in early for x in t) == multiplicity for t in triangles):
                seen.add(h)
                pending.append(h)
    return seen.isdisjoint(targets)


def temporal_cases(trajectories, forward, backward):
    results = {}
    for size in (2, 3):
        for projected in combinations('abcde', size):
            for early_left in (False, True):
                early = ''.join(projected)
                results[early, early_left] = tuple(
                    temporal_exclusion(early, early_left, after, trajectories, steps)
                    for after, steps in ((False, backward), (True, forward))
                )
    survivors = {}
    for early_left in (False, True):
        remaining = []
        for group in combinations('abcdef', 3):
            early = ''.join(group)
            ruled_out = False
            for omit in 'abcdef':
                retained = 'abcdef'.replace(omit, '')
                normalize = dict(zip(retained, 'abcde'))
                projected = ''.join(normalize[x] for x in early if x != omit)
                before, after = results[projected, early_left]
                if before or after:
                    ruled_out = True
                    break
            if not ruled_out:
                remaining.append(early)
        survivors[early_left] = remaining
    assert survivors == {
        False: [],
        True: ['ade', 'adf', 'aef', 'bde', 'bdf', 'bef', 'cde', 'cdf', 'cef', 'def'],
    }
    for early_left, remaining in survivors.items():
        side = 'left' if early_left else 'right'
        print(f'E spatially {side}: excluded {20 - len(remaining)}/20 inverted temporal placements; '
              f'remaining E triples {", ".join(remaining) or "none"}')


def main():
    start = 'edcba'
    trajectories = {h: tuple(states(start, h)) for h in raw_histories(start)}
    assert len(trajectories) == 768
    transitions = {
        h: {(m.target, () if m.family == 'K15' else gray(m)) for m in moves(start, h)}
        for h in trajectories
    }
    backward = defaultdict(set)
    for source, edges in transitions.items():
        for target, triangles in edges:
            backward[target].add((source, triangles))
    # Each of the ten ordered pair/triple placements occurs by adjoining
    # a new global minimum to the early pair before normalizing to six slots.
    counts = {}
    for early in combinations('abcde', 2):
        early = ''.join(early)
        counts[early] = continuation(early, trajectories, transitions)
    for early, (starts, reached, targets) in counts.items():
        print(f'{early}: {starts} shifted-join targets, {reached} reachable histories, '
              f'{targets} designated histories excluded')
    temporal_cases(trajectories, transitions, backward)


if __name__ == '__main__':
    main()
