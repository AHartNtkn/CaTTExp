"""Compare the group code with explicit squares, their pads and sorting schedules."""

from itertools import permutations, product
from random import Random

from interchange_rigid_group import Reduced, RigidGroup, StructuralPaths
from interchange_sorting_fiber import moves, raw_histories, states


def letters(group, code):
    stack = [code.forward]
    result = []
    while stack:
        rule = group.words.rules[stack.pop()]
        if len(rule) == 1:
            result.extend(rule)
        elif rule:
            stack.extend(~ref for ref in reversed(rule))
    return tuple(result)


def check_group_products():
    group = RigidGroup()
    pool = [(group.unit, ())]
    for i in range(4):
        a = group.head(4+i, 'head')
        pool.extend(((a, (2*i,)), (Reduced(a.inverse, a.forward), (2*i+1,))))
    rng = Random(82)
    for _ in range(600):
        (a, x), (b, y) = rng.choices(pool, k=2)
        raw = []
        for value in x + y:
            if raw and raw[-1] == value ^ 1:
                raw.pop()
            else:
                raw.append(value)
        c = group.join(a, b)
        assert letters(group, c) == tuple(raw)
        assert letters(group, Reduced(c.inverse, c.forward)) == tuple(v ^ 1 for v in reversed(raw))
        if len(raw) < 60:
            pool.append((c, tuple(raw)))
    print("600 compressed free products match signed stack reduction in both orientations.")


def check_towers():
    group = RigidGroup()
    e, l = (group.head(4, name) for name in 'EL')
    u, v = group.join(l, e), group.join(e, l)
    d = group.head(5, 'D')
    h = group.head(6, 'temporal square on D,D')

    def fold(values):
        value = group.unit
        for item in values:
            value = group.join(value, item)
        return value

    # A site changes from LE to EL once. A 5-history is a permutation of
    # those site updates. H exchanges the two schedules on adjacent sites.
    edges = paths = 0
    for n in range(2, 7):
        for start in permutations(range(n)):
            seen = {}
            pending = [(start, group.unit, ())]
            while pending:
                order, value, raw = pending.pop()
                key = letters(group, value)
                assert key not in seen or seen[key] == raw
                seen[key] = raw
                paths += 1
                previous = group.unit
                sites = [u]*n
                for pos, site in enumerate(order):
                    if pos + 1 < n and order[pos+1] == site - 1:
                        left = fold(sites[:site-1])
                        # Immediate 5-prefix outside the 4-action on H.
                        edge = group.left_action(previous, group.left_action(left, h))
                        alternate = group.left_action(group.join(previous, left), h)
                        assert group.equal_at_source(edge, alternate)
                        after = order[:pos] + (site-1, site) + order[pos+2:]
                        # Full contextual record includes both exterior pads
                        # at each rank, read directly from the named sites.
                        record = (order[:pos], tuple(sites[:site-1]), tuple(sites[site+1:]), order[pos+2:])
                        pending.append((after, group.join(value, edge), raw + (record,)))
                        edges += 1
                    previous = group.join(previous, group.left_action(fold(sites[:site]), d))
                    sites[site] = v
    print(f"{paths} six-dimensional paths and {edges} contextual square applications on up to six sites agree with the full records.")

    # Two actual 5-paths sweeping the same 2^k copies of D. At their
    # common source, reversing the order of two batches must be detected.
    sweep = d
    for k in range(12):
        direct = group.join(sweep, group.left_action(v, sweep))
        opposite = group.join(group.left_action(u, sweep), sweep)
        assert not group.equal_at_source(direct, opposite)
        if k % 2 == 0:
            quarter, pad = sweep, v
        else:
            two = group.join(pad, pad)
            alternate = fold(group.left_action(a, quarter) for a in
                             (group.unit, pad, two, group.join(two, pad)))
            assert group.equal_at_source(direct, alternate)
        sweep = direct
        u, v = group.join(u, u), group.join(v, v)
    print("Binary and quaternary sweeps agree at 4096 sites and distinguish reverse batch order.")


def check_structural_products():
    paths = StructuralPaths()
    count = 0
    high = 1 << 100
    for n in range(2, 9):
        for k in range(n):
            # Glue two actual n-globes along one k-face. Below k the
            # three incident k-cells have the same two hemispheres.
            def cells(rank, bounds, labels):
                if not rank:
                    return [paths.object(label) for label in labels]
                return [paths.globe((n, k, rank, label), *bounds) for label in labels]

            bounds = ()
            for j in range(k):
                bounds = cells(j, bounds, ('source', 'target'))
            x, y, z = cells(k, bounds, ('x', 'y', 'z'))
            left, right = (x, y), (y, z)
            for j in range(k+1, n):
                left = cells(j, left, ('left-', 'left+'))
                right = cells(j, right, ('right-', 'right+'))
            a, = cells(n, left, ('A',))
            b, = cells(n, right, ('B',))
            value = paths.product(k, a, b)
            for side in (0, 1):
                expected = (a, b)[side].face(k, side)
                assert paths.equal(value.face(k, side), expected)
                for j in range(k+1, n):
                    expected = paths.product(k, a.face(j, side), b.face(j, side))
                    assert paths.equal(value.face(j, side), expected)
            tags = [letters(paths.group, c.row(n)[0])[0] for c in (a, b)]
            observed = [v for v in letters(paths.group, value.row(n)[0]) if v in tags]
            assert observed == (tags[::-1] if (n-1-k) % 2 else tags)
            assert paths.equal(paths.product(k, a.elevate(high), b.elevate(high)), value.elevate(high))
            same = value.elevate(high)
            assert paths.equal(paths.product(high-2, same, same), same)
            assert paths.equal(paths.act(value.elevate(high-1), same, True), same)
            if k == n-2:
                forward = paths.chrono(paths.act(a.face(n-1, 0), b, True),
                                       paths.act(b.face(n-1, 1), a, False))
                reverse = paths.chrono(paths.act(b.face(n-1, 0), a, False),
                                       paths.act(a.face(n-1, 1), b, True))
                assert paths.equal(forward, value)
                assert not paths.equal(forward, reverse)
                for side in (0, 1):
                    assert paths.equal(forward.face(n-1, side), reverse.face(n-1, side))
            count += 1
    print(f"{count} glued-globe products agree on both hemispheres at every rank, head order and binary-degree elevation.")


def check_cancellation_obstruction():
    # The middle two swaps of the two 2-by-2 sweeps, after the common
    # first corner and before the common last corner, on four named slots.
    start, end = 'cdab', 'abcd'
    a, b = raw_histories(start, end)
    assert a[0] == b[0] and a[-1] == b[-1] and a[1:-1] != b[1:-1]
    assert any(step.family == 'K15' and step.target == b for step in moves(start, a))
    mid = list(states(start, a))[1]
    for p, q in product((a[1:-1], b[1:-1]), repeat=2):
        assert not any(step.family == 'K15' for step in moves(mid, p))
        assert list(states(mid, p))[-1] == list(states(mid, q))[-1]
    print("The contextual 2-by-2 crossing identifies the two full sweeps; their typed middle paths are distinct.")


if __name__ == '__main__':
    check_group_products()
    check_structural_products()
    check_towers()
    check_cancellation_obstruction()
