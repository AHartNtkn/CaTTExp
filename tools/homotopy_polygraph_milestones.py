"""Compare full semaphore fibres with the milestone order inside a binary component."""

from functools import cache
from itertools import combinations, product

from homotopy_polygraph_cubical_switch import cube_chain_betti
from homotopy_polygraph_semaphore import Ring, clock_chart
from homotopy_polygraph_two_resources import profiles


def orders(programs, states, serial, binary):
    """Build the process/hold order, then take transitive closure before restriction."""
    edges = {(i, k): {(i, k+1)} if k+1 < len(word) else set()
             for i, word in enumerate(programs) for k in range(len(word))}
    pos = [0] * len(programs)
    last_release = {}
    for i in serial:
        event = (i, pos[i])
        before, after = states[i][pos[i]:pos[i]+2]
        for r, users in binary.items():
            if i not in users:
                continue
            if not before[r] and after[r]:
                release = last_release.get((r, next(j for j in users if j != i)))
                if release is not None:
                    edges[release].add(event)
            if before[r] and not after[r]:
                last_release[r, i] = event
        pos[i] += 1
    # Serial order is topological for all these edges.
    for i in reversed(serial):
        pos[i] -= 1
        event = (i, pos[i])
        for successor in tuple(edges[event]):
            edges[event].update(edges[successor])
    return edges


def binary_pairs(states, binary):
    pairs = {}
    for r in binary:
        if any(all(row[r] == 0 for row in axis) for axis in states):
            continue
        changing = [i for i, axis in enumerate(states)
                    if any(row[r] == 0 for row in axis)]
        if len(changing) != 2:
            raise ValueError("record has no complete binary history or guard is not binary")
        pairs[r] = changing
    return pairs


def milestones(states, many):
    axes, events = [], []
    for i, axis in enumerate(states):
        masks = [sum(1 << k for k, r in enumerate(many) if row[r] == 0) for row in axis]
        changes = [j for j in range(len(axis)-1) if masks[j] != masks[j+1]]
        axes.append([masks[0]] + [masks[j+1] for j in changes])
        events.append([(i, j) for j in changes])
    return axes, events


def chains(axes, resources, enabled):
    goal = tuple(len(axis)-1 for axis in axes)
    @cache
    def visit(pos):
        if pos == goal:
            return [()] if all(any(row[t] >> r & 1 for row, t in zip(axes, pos))
                                for r in range(resources)) else []
        result = []
        active = [i for i, (t, bound) in enumerate(zip(pos, goal)) if t < bound]
        for length in range(1, len(active)+1):
            for tier in combinations(active, length):
                after = tuple(t + (i in tier) for i, t in enumerate(pos))
                if not enabled(pos, tier):
                    continue
                mask = 0
                for row, a, b in zip(axes, pos, after):
                    mask |= row[a] & row[b]
                if mask == (1 << resources)-1:
                    cell = sum(1 << i for i in tier)
                    result.extend((cell,) + tail for tail in visit(after))
        return result
    return visit((0,)*len(axes))


def compact(states, many, order):
    axes, events = milestones(states, many)
    preds = {e: [(i, j) for i, axis in enumerate(events) for j, p in enumerate(axis) if e in order[p]]
             for axis in events for e in axis}
    def enabled(pos, tier):
        return all(all(j < pos[k] for k, j in preds[events[i][pos[i]]]) for i in tier)
    size = sum(map(len, events))
    cells = chains(axes, len(many), enabled)
    return size, len(cells), cube_chain_betti(cells, size)


def compare(programs, initial, serial, many, binary, spatial=False):
    states = profiles(programs, initial)
    resources = len(initial[0])
    assert set(many).isdisjoint(binary) and set(many) | set(binary) == set(range(resources))
    pairs = binary_pairs(states, binary)
    pos = [0] * len(programs)
    for i in serial:
        pos[i] += 1
        assert all(any(axis[t][r] == 0 for axis, t in zip(states, pos)) for r in binary)
    assert pos == list(map(len, programs))
    order = orders(programs, states, serial, pairs)
    size, small, betti = compact(states, many, order)
    if spatial:
        axes = [[sum(1 << r for r in range(resources) if row[r] == 0) for row in axis] for axis in states]
        # Independently recover the component by square exchanges in the binary
        # grid. No inferred precedence is used to select the full chart strings.
        seen = {tuple(serial)}
        queue = list(seen)
        while queue:
            path = queue.pop()
            pos = [0]*len(axes)
            for j, (a, b) in enumerate(zip(path, path[1:])):
                if a != b:
                    other = path[:j] + (b, a) + path[j+2:]
                    if other not in seen and all(any(
                            not axis[t][r] and not axis[t + (i in (a,b))][r]
                            for i, (axis,t) in enumerate(zip(states,pos))) for r in binary):
                        seen.add(other)
                        queue.append(other)
                pos[a] += 1

        layout = Ring(len(axes))
        @cache
        def enabled(pos, tier):
            return clock_chart(layout, programs, states, pos, tier, resources)
        cells = [c for c in chains(axes, resources, enabled)
                 if tuple(i for tier in c for i in range(len(axes)) if tier >> i & 1) in seen]
        assert cube_chain_betti(cells, sum(map(len, programs))) == betti
        print(f'{len(cells)} full strings, {small} milestone strings, Betti {betti}.')
    return size, small, betti


def check():
    # The binary mutex orders two transfers. Which label of the binary base
    # was selected changes which comparisons survive on erasing its instructions.
    wrapped = lambda r: [('P', 2), ('P', r), ('V', 1-r), ('V', 2)]
    programs = [wrapped(0), wrapped(1), [('P', 0), ('V', 1)], [('P', 1), ('V', 0)]]
    initial = [(0,1,0), (1,0,0), (0,1,1), (1,0,1)]
    for a, b in ((0,1), (1,0)):
        compare(programs, initial, [a]*4+[b]*4+[2]*2+[3]*2, (0,1), (2,), True)

    # The high-arity guard here has an interior free window on the third
    # process and a disconnected free set on the first and second processes.
    words = [[('P',0),('V',0)], [('P',0),('V',0)], [('V',0),('P',0)], []]
    compare(words, [(0,), (0,), (1,), (1,)], [0,0,1,1,2,2], (0,), (), True)

    # Exponentially many binary components for two independent lists of mutex
    # excursions. None of these increasingly long instructions is a milestone.
    for repetitions in (1, 4, 16, 64):
        prefix = [('P',2), ('V',2)]*repetitions
        words = [prefix + [('P',r), ('V',1-r)] if i < 2 else [('P',r), ('V',1-r)]
                 for i, r in enumerate((0,0,1,1))]
        initial = [(0,1,0),(0,1,0),(1,0,1),(1,0,1)]
        left_first = [0]*(2*repetitions)+[1]*(2*repetitions)
        alternating = [0,0,1,1]*repetitions
        for prefix_order in (left_first, alternating):
            result = compare(words, initial, prefix_order + [0,0,1,1,2,2,3,3], (0,1), (2,))
            assert result == (8, 1360, (1,1))
        print(f'{sum(map(len, words))} instructions, eight milestones, a circle.')


if __name__ == '__main__':
    check()
