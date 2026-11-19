"""Execute the four-slot histories used to test the two-unary order invariant."""

from collections import defaultdict
from functools import cache
from itertools import combinations, permutations, product

from interchange_path_grading import History, cross, i_faces, r_faces, word
from interchange_slot_restriction import key, local_edges
from marked_swap_schedules import expansions


START = word('CDAB')
BRANCH = {slot: branch for branch, slots in enumerate(('AB', 'CD')) for slot in slots}
CROSSES = tuple((b, a) for a in 'AB' for b in 'CD')


def schedules(f, g):
    for history in permutations(CROSSES + ((f,), (g,))):
        state = list('CDAB')
        for event in history:
            if len(event) == 2:
                i = state.index(event[0])
                if state[i + 1:i + 2] != [event[1]]:
                    break
                state[i:i + 2] = event[::-1]
        else:
            yield history


def edges_by_schedule(histories):
    edges = defaultdict(set)
    for seq in histories:
        for after, atoms in local_edges(History(START, seq), BRANCH):
            assert after.events in histories
            edges[seq].add((after.events, tuple(atoms)))
        # The only nontrivial (K15) block uses the four crossings consecutively.
        for i in range(3):
            if set(seq[i:i + 4]) == set(CROSSES):
                for other in histories:
                    if other[:i] == seq[:i] and other[i + 4:] == seq[i + 4:]:
                        edges[seq].add((other, ()))
    return edges


def closure(start, graph):
    seen, pending = set(start), list(start)
    while pending:
        for v in graph[pending.pop()] - seen:
            seen.add(v)
            pending.append(v)
    return seen


def check_fiber(histories, edges, f, g, left, right):
    # Forget spectator vertices. This overapproximates a single Gray fiber.
    marked = (frozenset((key(f), key((f, left)))), frozenset((key(g), key((g, right)))))
    forward, backward = defaultdict(set), defaultdict(set)
    for seq, steps in edges.items():
        for after, atoms in steps:
            if any(atom not in marked for atom in atoms):
                continue
            assert len(atoms) <= 1  # The off-diagonal tensor pairs would also be present.
            bit = 1 << marked.index(atoms[0]) if atoms else 0
            for used in range(4):
                if used & bit:
                    continue
                u, v = (seq, used), (after, used | bit)
                forward[u].add(v)
                backward[v].add(u)
    cuts = defaultdict(set)
    for seq in histories:
        names = tuple(map(key, seq))
        for i in range(2, 5):
            early = frozenset(names[:i])
            if marked[0] <= early and marked[1].isdisjoint(early):
                cuts[early].add(seq)
    checks = vertices = 0
    for boundary in cuts.values():
        starts = {(p, 0) for p in boundary}
        ends = {(p, 3) for p in boundary}
        intermediate = closure(starts, forward) & closure(ends, backward)
        if intermediate:
            checks += 1
            vertices += len(intermediate)
            assert all(seq.index((f,)) < seq.index((g,)) for seq, _ in intermediate)
    return checks, vertices


def check():
    checks = vertices = 0
    for f, g in permutations('ABCD', 2):
        histories = set(schedules(f, g))
        edges = edges_by_schedule(histories)
        for left, right in permutations(set('ABCD') - {f, g}):
            if BRANCH[f] == BRANCH[left] or BRANCH[g] == BRANCH[right]:
                continue
            n, m = check_fiber(histories, edges, f, g, left, right)
            checks += n
            vertices += m
    assert checks and vertices
    print(f'Checked {vertices} intermediate states on {checks} nonempty four-slot cuts.')


def full_histories(slots, updates):
    @cache
    def visit(state, remaining):
        if state == slots and not remaining:
            return ((),)
        paths = []
        for i, (b, a) in enumerate(zip(state, state[1:])):
            if slots.index(b) > slots.index(a):
                after = state[:i] + (a, b) + state[i + 2:]
                paths.extend(((b, a),) + tail for tail in visit(after, remaining))
        for x in remaining:
            paths.extend(((x,),) + tail for tail in visit(state, remaining - {x}))
        return tuple(paths)
    return visit(slots[::-1], frozenset(updates))


@cache
def block_windows(state, order):
    blocks = []
    for lo, mid, hi in combinations(range(len(state) + 1), 3):
        b, a = state[lo:mid], state[mid:hi]
        if min(len(a), len(b)) < 2 or max(map(order.index, a)) >= min(map(order.index, b)):
            continue
        words = {tuple((j, i) for i, j in pattern) for pattern in expansions(a, b)}
        blocks.append((len(a) * len(b), words))
    return blocks


def with_equations(src, order):
    branch = {name: i for i, name in enumerate(order)}
    yield from local_edges(src, branch)
    state = tuple(x for x, _ in src.start)
    for i, event in enumerate(src.events):
        for size, words in block_windows(state, order):
            if src.events[i:i + size] in words:
                for w in words - {src.events[i:i + size]}:
                    after = History(src.start, src.events[:i] + w + src.events[i + size:])
                    assert after.end == src.end
                    yield after, ()
        if len(event) == 2:
            pos = state.index(event[0])
            state = state[:pos] + event[::-1] + state[pos + 2:]


def check_stationary_left():
    edges = rewrites = 0
    # G is the early crossing Z,z. F is a unary Y or the late crossing Y,y.
    for f_slots in (('Y',), ('Y', 'y')):
        for perm in permutations(('Z', 'z') + f_slots):
            if perm.index('Z') > perm.index('z') or (len(f_slots) == 2 and perm.index('Y') > perm.index('y')):
                continue
            order = ('X',) + perm
            start = word(order[::-1])
            p, d, g, f = key('XY'), key('ZY'), key('Zz'), key(f_slots)
            qs = (key('XZ'), key('Xz'))
            needs_frame = order.index('Z') < order.index('Y')
            updates = f_slots if len(f_slots) == 1 else ()
            for seq in full_histories(order, updates):
                names = list(map(key, seq))
                if not (max(names.index(q) for q in qs) < names.index(p) < names.index(g)
                        and names.index(p) < names.index(f)):
                    continue
                if needs_frame and names.index(f) > names.index(d):
                    continue
                for after, atoms in with_equations(History(start, seq), order):
                    if needs_frame and any(({f, d} <= a or {g, d} <= a) for a in atoms):
                        continue
                    dest = list(map(key, after.events))
                    if max(dest.index(q) for q in qs) > dest.index(p):
                        continue
                    assert dest.index(p) < dest.index(f) and dest.index(p) < dest.index(g)
                    if needs_frame:
                        assert dest.index(f) < dest.index(d)
                    edges += 1
                    # Block equations are explicitly yielded with a tuple; zero-Gray
                    # inner generators use a list of atoms in local_edges.
                    rewrites += isinstance(atoms, tuple)
    assert edges > rewrites > 0
    print(f'Checked the stationary-left barrier on {edges} transitions, including {rewrites} block rewrites.')


def check_disjoint_routes():
    a, b, c, d, e, f, g = map(word, 'ABCDEFG')
    tau = r_faces(cross(a, b), c)
    bare = i_faces(cross(d, e), cross(f, g))
    start = tau[0].pad(right=bare[0].start).then(bare[0].pad(left=tau[0].end))
    end = tau[1].pad(right=bare[1].start).then(bare[1].pad(left=tau[1].end))
    order = tuple('ABCDEFG')
    states = {}
    for seq in permutations(start.events):
        names = list(start.start)
        for event in seq:
            b_slot, a_slot = ((x, 0) for x in event)
            i = names.index(b_slot)
            if names[i + 1:i + 2] != [a_slot]:
                break
            names[i:i + 2] = (a_slot, b_slot)
        else:
            states[seq] = History(start.start, seq)
    forward, backward = defaultdict(set), defaultdict(set)
    for seq, history in states.items():
        for after, atoms in with_equations(history, order):
            assert after.events in states
            if seq != after.events:
                forward[seq].add(after.events)
                backward[after.events].add(seq)
    relevant = closure({start.events}, forward) & closure({end.events}, backward)
    middle = relevant - {start.events, end.events}
    assert len(relevant) == 4 and len(middle) == 2
    assert forward[start.events] & relevant == middle
    for seq in middle:
        assert forward[seq] & relevant == {end.events}
    late_first = tau[0].events + bare[1].events
    early_first = tau[1].events + bare[0].events
    assert middle == {late_first, early_first}

    # In either direction of inner naturality a variation comparing the
    # two triangle faces against a one-event spatial operand must use
    # all three triangle/event pairs in its inner product.
    moving = cross(d, e)
    for spatial_left in (False, True):
        labels = []
        for face in tau:
            left, right = (face, moving) if spatial_left else (moving, face)
            before, after = i_faces(left, right)
            assert before.events == right.events + left.events
            assert after.events == left.events + right.events
            labels.append({frozenset((key(x), key(y))) for x in left.events for y in right.events})
        assert labels[0] == labels[1] and len(labels[0]) == 3
        kernel_label = frozenset((key('DE'), key('FG')))
        assert kernel_label not in labels[0]
    print(f'Enumerated all {len(states)} histories of the seven-slot example; '
          'its full 4-path interval has exactly the two elementary routes.')


def compose(a, b):
    return tuple(b[i] for i in a)


def check_local_groups():
    maps = list(product(range(3), repeat=3))
    unit = (0, 1, 2)
    orders = set()
    for u, v in product(maps, repeat=2):
        monoid, pending = {unit}, [unit]
        while pending:
            a = pending.pop()
            for b in (u, v):
                c = compose(a, b)
                if c not in monoid:
                    monoid.add(c)
                    pending.append(c)
        idem = {e for e in monoid if compose(e, e) == e}
        e = next(e for e in idem if all(f == e or compose(e, f) != f or compose(f, e) != f
                                        for f in idem))
        local = {compose(compose(e, a), e) for a in monoid}
        a, b = (compose(compose(e, z), e) for z in (u, v))
        inverse = next(z for z in local if compose(a, z) == compose(z, a) == e)
        step = compose(inverse, b)
        state = e
        for k in range(1, len(local) + 1):
            state = compose(state, step)
            if state == e:
                orders.add(k)
                break
        else:
            raise AssertionError('The sandwiched route failed to return to the idempotent.')
    assert orders == {1, 2, 3}
    print('Checked the idempotent sandwich on all 729 pairs of three-point transformations.')


if __name__ == '__main__':
    check()
    check_local_groups()
    check_stationary_left()
    check_disjoint_routes()
