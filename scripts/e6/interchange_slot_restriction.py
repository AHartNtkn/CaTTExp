"""Test slot incidence, contractions, and the first cross-slot obstructions."""

from functools import cache
from itertools import combinations, permutations, product

from interchange_path_grading import History, cross, families, i_faces, r_faces, t_faces, word
from marked_swap_schedules import expansions


def key(event):
    # Each concrete history in this check has at most one update per slot.
    return frozenset(event)


def order_on(slot, history):
    return tuple(key(e) for e in history.events if slot in e)


def mixed_support(history, opposite):
    atoms = []
    for event in history.events:
        for slot, _ in opposite:
            incidence = {key(event)} | {key((x, slot)) for x in event}
            atoms.append(frozenset(incidence))
    return atoms


def check_incidence(source, target, atoms):
    assert source.start == target.start and source.end == target.end
    for slot, _ in source.start:
        first, last = order_on(slot, source), order_on(slot, target)
        assert set(first) == set(last) and len(set(first)) == len(first)
        changed = {frozenset((e, f)) for e, f in combinations(first, 2)
                   if last.index(e) > last.index(f)}
        expected = {frozenset(pair) for atom in atoms
                    for pair in combinations([e for e in atom if slot in e], 2)}
        assert changed == expected


def history_pairs():
    # Mixed unary and binary steps in both spatial operands.
    for a, b in product(set(families('AB')), set(families('CD'))):
        x, y = a.start, b.start
        for faces, atoms in ((r_faces(a, y), mixed_support(a, y)),
                             (t_faces(x, b), mixed_support(b, x)),
                             (i_faces(a, b), [])):
            check_incidence(*faces, atoms)
        s = b.pad(right=x).then(cross(x, b.end)).then(a.pad(right=b.end))
        u = a.pad(left=y).then(b.pad(right=a.end)).then(cross(a.end, b.end))
        check_incidence(s, u, mixed_support(a, b.end))
        yield 1


def erase(history, retained):
    start = tuple(pair for pair in history.start if pair[0] in retained)
    result = History(start, tuple(e for e in history.events if set(e).issubset(retained)))
    assert result.end == tuple(pair for pair in history.end if pair[0] in retained)
    return result


def seven_slot_test():
    a, b, c, d, e, f, g = (word(x) for x in 'ABCDEFG')
    # On three outer slots the two faces of tau are the two braid schedules.
    tau = r_faces(cross(a, b), c)
    assert tau == t_faces(a, cross(b, c))
    inner = i_faces(cross(d, e), cross(f, g))
    tau = tuple(p.pad(right=inner[0].start) for p in tau)
    inner = tuple(p.pad(left=tau[0].end[:3]) for p in inner)
    assert tau[0].end == inner[0].start
    for size in range(8):
        for retained in combinations('ABCDEFG', size):
            left = [erase(p, retained) for p in tau]
            right = [erase(p, retained) for p in inner]
            assert left[0].end == right[0].start
            assert (left[0] != left[1]) == set('ABC').issubset(retained)
            assert (right[0] != right[1]) == set('DEFG').issubset(retained)


def incidence_rectangles():
    # On five slots choose two triangles sharing the middle slot C.
    # The first lies to its left and the second to its right.
    a, b, c, d, e = (word(x) for x in 'ABCDE')
    first = r_faces(cross(a, b), c)
    second = r_faces(cross(c, d), e)
    # After CBA becomes ABC, pass E,D across the stationary A,B
    # to put EDC together. The bridge has no incidence on C.
    spectators = word('ED')
    first = tuple(p.pad(left=spectators) for p in first)
    bridge = cross(word('AB'), spectators).pad(right=c)
    second = tuple(p.pad(left=word('AB')) for p in second)
    assert first[0].end == bridge.start and bridge.end == second[0].start
    early = {key(('A', 'C')), key(('B', 'C'))}
    late = {key(('C', 'D')), key(('C', 'E'))}
    for p, q in product(first, second):
        projection = order_on('C', p.then(bridge).then(q))
        assert set(projection[:2]) == early and set(projection[2:]) == late


def check_kernel_then_triangle():
    x, a, b, c, z = (word(k) for k in 'XABCZ')
    # Central slots stay ordered A,B,C. Z moves right and X moves left.
    pure = i_faces(cross(a, z), cross(x, c).pad(left=b))
    triangle = tuple(p.pad(left=a, right=c) for p in r_faces(cross(x, b), z))
    assert pure[0].start == word('ZABCX')
    assert pure[0].end == triangle[0].start == word('AZBXC')
    for p, t in product(pure, triangle):
        combined = p.then(t)
        assert order_on('Z', combined)[0] == key('ZA')
        assert order_on('X', combined)[0] == key('XC')
        assert key('XZ') in order_on('Z', combined)[1:]
        assert key('XZ') in order_on('X', combined)[1:]


def local_edges(history, branch):
    """Instantiate the structural 4-edges on each spatial and temporal window."""
    n = history.mass
    for start, end in combinations(range(n + 1), 2):
        state = History(history.start, history.events[:start]).end
        active = history.events[start:end]
        for lo, mid, hi in combinations(range(len(state) + 1), 3):
            left, right = state[lo:mid], state[mid:hi]
            left_names, right_names = ({x for x, _ in side} for side in (left, right))
            lhist = History(left, tuple(e for e in active if set(e) <= left_names))
            rhist = History(right, tuple(e for e in active if set(e) <= right_names))
            candidates = []
            if lhist.mass and rhist.mass:
                candidates.append((i_faces(lhist, rhist), []))
            # At the source of any outer move b is still to the left of a.
            if max(branch[x] for x in right_names) < min(branch[y] for y in left_names):
                if rhist.mass:
                    ra = mixed_support(rhist, left)
                    candidates.append((r_faces(rhist, left), ra))
                    if lhist.mass:
                        source = lhist.pad(right=right).then(cross(right, lhist.end)).then(
                            rhist.pad(right=lhist.end))
                        target = rhist.pad(left=left).then(lhist.pad(right=rhist.end)).then(
                            cross(rhist.end, lhist.end))
                        candidates.append(((source, target), ra))
                if lhist.mass:
                    candidates.append((t_faces(right, lhist), mixed_support(lhist, right)))
            for (source, target), atoms in candidates:
                if source.events == active:
                    after = History(history.start, history.events[:start] + target.events + history.events[end:])
                    assert after.end == history.end
                    yield after, atoms


def right_operand_barrier():
    checked = 0
    p, q, g = key('XY'), key('XZ'), key('Z')
    incident_atom = frozenset((g, key('ZY')))
    for y_order, z_order in ((1, 2), (2, 1), (1, 1)):
        branch = {'X': 0, 'Y': y_order, 'Z': z_order}
        initial = tuple(sorted('XYZ', key=branch.get, reverse=True))
        events = [(b, a) for i, b in enumerate(initial) for a in initial[i + 1:]
                  if branch[b] > branch[a]] + [('Y',), ('Z',)]
        for order in permutations(events):
            names = list(map(key, order))
            if not names.index(q) < names.index(p) < names.index(g):
                continue
            state = list(initial)
            for event in order:
                if len(event) == 2:
                    i = state.index(event[0])
                    if state[i + 1:i + 2] != [event[1]]:
                        break
                    state[i:i + 2] = event[::-1]
            else:
                src = History(word(initial), order)
                for after, atoms in local_edges(src, branch):
                    if z_order < y_order and incident_atom in atoms:
                        continue
                    dest = list(map(key, after.events))
                    if dest.index(q) < dest.index(p):
                        assert dest.index(p) < dest.index(g)
                        checked += 1
    assert checked
    print(f'Checked the right-operand order barrier on {checked} contextual 4-edges.')


def has_kernel_cycle(groups):
    slots = tuple(x for group in groups for x in group)
    branch = {x: i for i, group in enumerate(groups) for x in group}
    start = tuple(x for group in reversed(groups) for x in group)

    @cache
    def continuations(state):
        if state == slots:
            return ((),)
        result = []
        for i, (b, a) in enumerate(zip(state, state[1:])):
            if branch[a] < branch[b]:
                tail = state[:i] + (a, b) + state[i + 2:]
                result.extend(((a, b),) + p for p in continuations(tail))
        return tuple(result)

    @cache
    def rules(state):
        blocks = []
        for lo, mid, hi in combinations(range(len(slots) + 1), 3):
            b, a = state[lo:mid], state[mid:hi]
            if min(len(a), len(b)) < 2 or max(branch[x] for x in a) >= min(branch[x] for x in b):
                continue
            blocks.append((len(a) * len(b), expansions(a, b)))
        return blocks

    paths = continuations(start)
    parent = {p: p for p in paths}

    def root(p):
        while parent[p] != p:
            parent[p] = parent[parent[p]]
            p = parent[p]
        return p

    directed = []
    for path in paths:
        state = start
        for i, (a, b) in enumerate(path):
            for width, alternatives in rules(state):
                if path[i:i + width] in alternatives:
                    for q in alternatives:
                        parent[root(path)] = root(path[:i] + q + path[i + width:])
            pos = state.index(b)
            assert state[pos + 1] == a
            if i + 1 < len(path):
                c, d = path[i + 1]
                if state.index(d) < pos - 1 and state[state.index(d) + 1] == c:
                    directed.append((path, path[:i] + ((c, d), (a, b)) + path[i + 2:]))
            state = state[:pos] + (a, b) + state[pos + 2:]
    graph = {root(p): set() for p in paths}
    for p, q in directed:
        graph[root(p)].add(root(q))
    # Topological elimination detects both self-loops and longer cycles.
    incoming = dict.fromkeys(graph, 0)
    for targets in graph.values():
        for q in targets:
            incoming[q] += 1
    ready = [p for p, n in incoming.items() if n == 0]
    visited = 0
    while ready:
        p = ready.pop()
        visited += 1
        for q in graph[p]:
            incoming[q] -= 1
            if incoming[q] == 0:
                ready.append(q)
    return visited != len(graph)


def check_shapes():
    count = cyclic = 0
    for n in range(1, 6):
        for bits in product((False, True), repeat=n - 1):
            borders = [i + 1 for i, present in enumerate(bits) if present]
            groups = [tuple(range(i, j)) for i, j in zip([0] + borders, borders + [n])]
            found = has_kernel_cycle(groups)
            assert found == any(2 <= i <= n - 2 for i in borders)
            count += 1
            cyclic += found
    print(f'Computed the crossing-schedule quotient and cycle graph on {count} shapes; {cyclic} have a loop.')


def check_pair_projections(r):
    orders = list(permutations(range(r)))
    pairs = list(combinations(range(r), 2))
    # Each coordinate is the schedule after erasing all but two groups.
    signatures = {p: frozenset((i, j) for i, j in pairs
                               if tuple(x for x in p if x in (i, j)) == (j, i))
                  for p in orders}
    assert len(set(signatures.values())) == len(orders)
    reachable = {p: {p} for p in orders}
    for p in sorted(orders, key=lambda x: len(signatures[x])):
        for i in range(r - 1):
            if p[i] > p[i + 1]:
                swapped = p[:i] + (p[i + 1], p[i]) + p[i + 2:]
                reachable[p].update(reachable[swapped])
        predicted = {q for q in orders if signatures[q] <= signatures[p]}
        assert reachable[p] == predicted
    comparable = sum(map(len, reachable.values()))
    print(f'Checked all {len(orders) ** 2} schedule pairs on {r} groups; '
          f'{comparable} are reachable in the directed sorting graph.')


if __name__ == '__main__':
    print(f'Checked four slot-incidence identities on each of {sum(history_pairs())} pairs of histories.')
    seven_slot_test()
    print('Checked all 128 contractions of the seven-slot elementary rectangle.')
    incidence_rectangles()
    print('Checked the four corners of the two mixed triangles on five slots.')
    check_shapes()
    right_operand_barrier()
    check_pair_projections(6)
    check_kernel_then_triangle()
    print('Checked the four corners for an inner exchange followed by a triple on a (1,3,1) shape.')
