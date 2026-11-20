"""Decide two-resource typed rings with no same-resource excursions."""

from collections import Counter
from itertools import combinations, product

from homotopy_polygraph_parking import acquisition_before_release
from homotopy_polygraph_semaphore import Ring, clock_chart, histories, typed_presentation


def two_resource_homotopical(graphs):
    transfers = []
    for graph in graphs:
        for r in (0, 1):
            if acquisition_before_release(graph, ('P', r), ('V', r)):
                raise ValueError("control graph admits a same-resource excursion")
        transfers.append({r for r in (0, 1) if
                          acquisition_before_release(graph, ('P', r), ('V', 1 - r))})
    active = [choices for choices in transfers if choices]
    if len(active) < 4:
        return True
    return not any(0 in a and 1 in b for i, a in enumerate(active)
                   for j, b in enumerate(active) if i != j)


def profiles(programs, initial):
    states = []
    for program, start in zip(programs, initial, strict=True):
        row = [Counter(dict(enumerate(start)))]
        for op in program:
            next_state = row[-1].copy()
            if op is not None:
                kind, r = op
                next_state[r] += 1 if kind == 'P' else -1
                if next_state[r] < 0:
                    raise ValueError("negative resource count")
            row.append(next_state)
        states.append(row)
    return states


def predicted_betti(states):
    if any(all(row[t][r] for row in states) for t in (0, -1) for r in (0, 1)):
        return ()
    covered = set()
    departures = []
    for row in states:
        zeros = [set(i for i, state in enumerate(row) if state[r] == 0) for r in (0, 1)]
        if any(len(z) and len(z) != max(z) - min(z) + 1 for z in zeros):
            raise ValueError("disconnected zero interval")
        if not all(zeros) or zeros[0] & zeros[1]:
            covered.update(r for r, z in enumerate(zeros) if z)
        else:
            departures.append(int(max(zeros[1]) < min(zeros[0])))
    if covered:
        return (1,)
    if len(set(departures)) < 2:
        return ()
    n = len(departures)
    if n == 2:
        return ()
    if n == 3:
        return (2,)
    return (1,) + (0,) * (n - 4) + (1,)


def check_spatial(name, programs, initial, *, euler_only=False):
    layout = Ring(len(programs))
    states = profiles(programs, initial)
    expected = predicted_betti(states)
    legal = set()
    for pos in product(*(range(len(row)) for row in states)):
        axes = [i for i, t in enumerate(pos) if t < len(programs[i])]
        for n in range(len(axes) + 1):
            for moving in combinations(axes, n):
                ends = [row[t] | row[t + (i in moving)] for i, (row, t) in enumerate(zip(states, pos))]
                capacity = all(any(not row[r] for row in ends) for r in (0, 1))
                spatial = clock_chart(layout, programs, states, pos, moving, 2)
                assert spatial == capacity
                if spatial:
                    legal.add((pos, moving))
    # A tier of size k contributes k-1 to the permutohedral cell dimension.
    origin = (0,) * len(programs)
    end = tuple(map(len, programs))
    euler = Counter({origin: 1}) if (origin, ()) in legal else Counter()
    for pos, moving in sorted(legal):
        if moving:
            nxt = tuple(t + (i in moving) for i, t in enumerate(pos))
            euler[nxt] += (-1) ** (len(moving) - 1) * euler[pos]
    assert euler[end] == sum((-1) ** i * b for i, b in enumerate(expected))
    if euler_only:
        print(f'{name}: {len(legal)} spatial cubes, Euler characteristic {euler[end]}')
        return
    # Empty histories have no chain groups.
    reachable = {(0,) * len(programs)} if ((0,) * len(programs), ()) in legal else set()
    for pos, moving in sorted(legal):
        if pos in reachable and len(moving) == 1:
            reachable.add(tuple(t + (i in moving) for i, t in enumerate(pos)))
    actual = list(histories(programs, legal)) if tuple(map(len, programs)) in reachable else []
    while actual and not actual[-1]:
        actual.pop()
    assert tuple(actual) == expected, (name, expected, actual)
    print(f'{name}: {len(legal)} spatial cubes, Betti {tuple(actual)}')


def check():
    def route(r):
        return (('P', r), ('V', 1 - r))

    start = [(0, 1), (1, 0)]

    def graph(word):
        return [(i, op, i + 1) for i, op in enumerate(word)]

    for directions in product(range(2), repeat=4):
        graphs = [graph(route(r)) for r in directions]
        assert two_resource_homotopical(graphs) == (len(set(directions)) == 1)
    both = graph(route(0)) + [(3, ('P', 1), 4), (4, None, 4), (4, ('V', 0), 5)]
    assert not two_resource_homotopical([both] + [graph(route(0))] * 3)
    assert two_resource_homotopical([both] * 3 + [[]])

    for directions in ((0, 1), (0, 0, 1), (0, 0, 0, 1), (0, 0, 1, 1)):
        programs = [route(r) for r in directions]
        initial = [start[r] for r in directions]
        while len(programs) < 4:
            programs.append(())
            initial.append((1, 1))
        if directions == (0, 0, 1, 1):
            print(f'{len(typed_presentation(Ring(4), programs))} typed declarations')
        check_spatial(str(directions), programs, initial)
    directions = (0, 0, 0, 1, 1)
    check_spatial('five transfers', [route(r) for r in directions],
                  [start[r] for r in directions], euler_only=True)
    check_spatial('one stationary witness', [route(0), route(1), route(0), ()],
                  [start[0], start[1], start[0], (0, 1)])
    check_spatial('overlapping zero intervals',
                  [route(0), route(1), route(0), (('V', 1), ('P', 0))],
                  [start[0], start[1], start[0], start[0]])
    check_spatial('both minima interior', [(('V', 0), *route(0), ('P', 1)),
                                          route(1), route(0), route(1)],
                  [(1, 1), start[1], start[0], start[1]])


if __name__ == '__main__':
    check()
