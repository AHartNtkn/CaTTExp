"""Decide the one-resource ring and count strict labels of a fixed record."""

from collections import Counter
from itertools import combinations, product
from math import comb

from homotopy_polygraph_semaphore import Ring, clock_chart, histories


def acquisition_before_release(edges, acquisition='P', release='V'):
    """Return whether a finite control graph has a walk with P before V."""
    outgoing = {}
    pending = set()
    for source, action, target in edges:
        outgoing.setdefault(source, []).append((action, target))
        if action == acquisition:
            pending.add(target)
    visited = set()
    while pending:
        state = pending.pop()
        visited.add(state)
        for action, target in outgoing.get(state, ()):
            if action == release:
                return True
            if target not in visited:
                pending.add(target)
    return False


def one_resource_homotopical(graphs):
    return sum(acquisition_before_release(edges) for edges in graphs) <= 2


def count_path(word, initial):
    values = [initial]
    for action in word:
        values.append(values[-1] + {'P': 1, 'V': -1, 'N': 0}[action])
    return values


def strict_label_count(words, initial):
    """Endpoint components at fixed control words, counts and valid gaps."""
    counts = [count_path(w, m) for w, m in zip(words, initial, strict=True)]
    if any(min(row) < 0 for row in counts):
        raise ValueError("release from an empty list")
    if all(row[0] for row in counts) or all(row[-1] for row in counts):
        return 0
    core = []
    for word, row in zip(words, counts):
        if 'V' in word.partition('P')[2]:
            core.append(row)
        elif min(row) == 0:
            return 1
    if len(core) > 2:
        raise ValueError("more than two unparked coordinates")
    # With every parked process holding, a sole remaining process must stay free.
    if len(core) < 2:
        return int(bool(core) and max(core[0]) == 0)
    runs = [int(row[0] > 0) + sum(a == 0 and b > 0 for a, b in zip(row, row[1:]))
            for row in core]
    total = sum(runs)
    if total <= 1:
        return 1
    for endpoint in (0, -1):
        for i, row in enumerate(core):
            if row[endpoint] > 0:
                runs[i] -= 1
    return 0 if min(runs) < 0 else comb(sum(runs), runs[0])


def spatial_grid(words, initial, layout):
    programs = [tuple(None if op == 'N' else (op, 0) for op in word) for word in words]
    states = [[Counter({0: x}) for x in count_path(word, start)]
              for word, start in zip(words, initial)]
    cubes = set()
    for pos in product(*(range(len(row)) for row in states)):
        axes = [i for i, t in enumerate(pos) if t + 1 < len(states[i])]
        for size in range(len(axes) + 1):
            for moving in combinations(axes, size):
                if clock_chart(layout, programs, states, pos, moving, 1):
                    cubes.add((pos, moving))
    return programs, cubes


def serial_components(words, initial):
    """Enumerate all serial histories, then quotient by legal square exchanges."""
    states = [count_path(w, m) for w, m in zip(words, initial)]

    def legal(pos):
        return any(row[t] == 0 for row, t in zip(states, pos))

    def advance(pos, i):
        return tuple(t + (j == i) for j, t in enumerate(pos))

    def serial(pos, prefix):
        if legal(pos):
            if pos == tuple(map(len, words)):
                yield prefix
            for i, t in enumerate(pos):
                if t < len(words[i]):
                    yield from serial(advance(pos, i), prefix + (i,))

    pending = set(serial((0,) * len(words), ()))
    components = 0
    while pending:
        components += 1
        stack = [pending.pop()]
        while stack:
            path = stack.pop()
            for k, (a, b) in enumerate(zip(path, path[1:])):
                if a != b:
                    other = path[:k] + (b, a) + path[k + 2:]
                    # All four corners are legal iff the whole square is legal.
                    if other in pending:
                        pending.remove(other)
                        stack.append(other)
    return components


def check():
    branch = [(0, 'P', 1), (0, 'V', 2), (1, 'N', 1)]
    loop = [(0, 'P', 1), (1, 'N', 1), (1, 'P', 2), (2, 'V', 0)]
    assert not acquisition_before_release(branch) and acquisition_before_release(loop)
    assert one_resource_homotopical([loop, branch, loop, branch])
    assert not one_resource_homotopical([loop, branch, loop, loop])

    cases = 0
    # At most two peak words. The other processes can cover a free valley,
    # remain positive throughout, or hold at either endpoint.
    for left, right in product(('', 'P', 'V', 'PV', 'VP', 'VPV', 'PVP'), repeat=2):
        for valley in ('', 'V', 'P', 'VP'):
            words = (left, right, valley, '')
            minima = [-min(count_path(w, 0)) for w in words]
            for offsets in product(range(2), repeat=4):
                initial = tuple(m + b for m, b in zip(minima, offsets))
                assert strict_label_count(words, initial) == serial_components(words, initial), (words, initial)
                cases += 1
    print(f'{cases} endpoint records agree with the serial exchange quotient.')
    layout = Ring(4)
    for words, initial, expected in [
            (('PV', 'PV', 'VP', ''), (0, 0, 1, 1), (1,)),
            (('PV', 'PV', 'VP', ''), (0, 0, 2, 1), (2,)),
            (('PVPV', 'PVPV', '', ''), (0, 0, 1, 1), (6,)),
            (('PV', 'PV', 'PV', ''), (0, 0, 0, 1), (1, 1))]:
        programs, cubes = spatial_grid(words, initial, layout)
        betti = histories(programs, cubes)
        assert betti[:len(expected)] == expected and not any(betti[len(expected):])


if __name__ == '__main__':
    check()
