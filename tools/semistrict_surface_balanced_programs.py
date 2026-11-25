"""Compile serial scalar movies to binary updates with the fewest complete packet paths.

The JSON certificate contains the expanded movie and the edge and event images
accepted by semistrict_surface_scalar_circuits.decode. A pure cut without any
updates needs no movie compilation.
"""
from argparse import ArgumentParser
from collections import deque
from itertools import combinations, product
import json
from pathlib import Path

from semistrict_surface_gate_forests import cable
from semistrict_surface_scalar_circuits import decode
from semistrict_surface_scalar_leaves import read_edges, sample


def path_cover(steps, wire_count):
    """Find a minimum multiset of paths visiting each wire and twice each positive site."""
    edges = [[] for _ in range(wire_count)]
    for _, ins, outs, _ in steps:
        copies = 2 if ins and outs else int(bool(ins or outs))
        for _ in range(copies):
            marker = len(edges)
            edges.append(outs.copy())
            for g in ins:
                edges[g].append(marker)

    # Record one first hop along each strict comparability of the obligations.
    hop = []
    for root in range(len(edges)):
        row = {}
        queue = deque((x, x) for x in edges[root])
        while queue:
            x, first = queue.popleft()
            if x not in row:
                row[x] = first
                queue.extend((y, first) for y in edges[x])
        hop.append(row)

    # Bipartite matching on comparabilities. At termination the alternating
    # forest also certifies the minimum by an antichain of the same size.
    succ, pred = {}, {}
    while True:
        left = set(range(len(edges))) - succ.keys()
        queue = deque(sorted(left))
        right = {}
        end = None
        while queue and end is None:
            x = queue.popleft()
            for y in hop[x]:
                if y in right or succ.get(x) == y:
                    continue
                right[y] = x
                if y not in pred:
                    end = y
                    break
                z = pred[y]
                if z not in left:
                    left.add(z)
                    queue.append(z)
        if end is None:
            break
        while end is not None:
            x = right[end]
            pred[end] = x
            old = succ.get(x)
            succ[x] = end
            end = old

    incoming = [[] for _ in edges]
    for x, targets in enumerate(edges):
        for y in targets:
            incoming[y].append(x)
    paths = []
    for first in sorted(set(range(len(edges))) - pred.keys()):
        route = [first]
        while incoming[route[-1]]:
            route.append(incoming[route[-1]][0])
        route.reverse()
        x = first
        while x in succ:
            target = succ[x]
            while x != target:
                x = hop[x][target]
                route.append(x)
        while edges[route[-1]]:
            route.append(edges[route[-1]][0])
        paths.append(route)
    lower = sorted(left - right.keys())
    assert len(lower) == len(paths)
    assert all(y not in hop[x] and x not in hop[y] for x, y in combinations(lower, 2))
    assert set().union(*map(set, paths)) == set(range(len(edges)))
    widths = [0] * wire_count
    for route in paths:
        for g in route:
            if g < wire_count:
                widths[g] += 1
    return widths, paths, lower


def representatives(wires, widths):
    return [packet for w in wires for packet in [[w]] + [[] for _ in range(widths[w] - 1)]]


def instructions(ins, outs, widths):
    """Local slot, input count, decoded output packets, and original event flag."""
    start = representatives(ins, widths)
    goal = representatives(outs, widths)
    if not start and not goal:
        yield 0, 0, [[]], True
        yield 0, 1, [], False
        return
    if len(start) == len(goal) == 2:
        yield 0, 2, goal, True
        return
    if start:
        gathered = start[-1]
        for j in reversed(range(len(start) - 1)):
            gathered = start[j] + gathered
            yield j, 2, [gathered, []], False
        if goal:
            assert len(start) == len(goal) >= 2
            yield 0, 2, [outs, []], True
        else:
            for j in reversed(range(len(start))):
                yield j, 1, [], j == 0
            return
    else:
        for j in range(len(goal)):
            yield j, 0, [outs if j == 0 else []], j == 0
    rest = list(outs)
    for j, packet in enumerate(goal[:-1]):
        rest = rest[len(packet):]
        yield j, 2, [packet, rest], False


def encode(data):
    initial, final, source, _, steps = read_edges(data)
    widths, paths, lower = path_cover(steps, len(source))
    initial_packets = representatives(initial, widths)
    labels = initial_packets.copy()
    changes, seams, owners = [], [], []
    for i, (below, ins, outs, above) in enumerate(steps):
        offset = sum(widths[w] for w in below)
        for slot, count, packets, centre in instructions(ins, outs, widths):
            changes.append((offset + slot, count, len(packets)))
            labels.extend(packets)
            seams.append([])
            owners.append(i if centre else None)
        if i < len(data['seams']):
            seams[-1] = list(cable(data['seams'][i], [widths[g] for g in below + outs + above]))
    movie = sample([f'p{i}' for i in range(len(initial_packets))], changes, seams[:-1])
    cert = dict(movie=movie, edge_packets=labels, event_images=owners, widths=widths,
                complete_paths=paths, antichain=lower)
    assert decode(cert) == (initial, final, steps, [list(s) for s in data['seams']])
    return cert


def frontier_width(steps, initial):
    """Independent lower bound: maximize occupied slots over mixed simultaneous frontiers."""
    best = 0
    seen = set()

    def visit(done, live):
        nonlocal best
        if done in seen:
            return
        seen.add(done)
        enabled = [(i, set(ins), set(outs)) for i, (_, ins, outs, _) in enumerate(steps)
                   if i not in done and set(ins) <= live]
        # For positive events, one can choose independently between their
        # input ports and two obligations on the simultaneous jump.
        best = max(best, len(live) + sum(max(0, 2 - len(ins)) for _, ins, _ in enabled))
        for i, ins, outs in enabled:
            visit(done | {i}, (live - ins) | outs)

    visit(frozenset(), set(initial))
    return best


def audit():
    cases = positive = 0

    def check(data):
        nonlocal cases, positive
        cert = encode(data)
        init, _, _, _, steps = read_edges(data)
        shapes = {(len(ins), len(outs)) for _, ins, outs, _ in read_edges(cert['movie'])[-1]}
        if all(ins and outs for _, ins, outs, _ in steps):
            assert shapes == {(2, 2)}
            assert len(cert['complete_paths']) == frontier_width(steps, init)
            assert sum(cert['widths'][w] for w in init) == len(cert['antichain'])
            positive += 1
        if all(outs for _, _, outs, _ in steps):
            assert (1, 0) not in shapes
        if all(ins for _, ins, _, _ in steps):
            assert (0, 1) not in shapes
        cases += 1
        return cert

    for p, q, r in product(range(4), repeat=3):
        for sign in (-1, 1):
            check(sample(['a'] * (p + 2), [(1, p, q), (1, q, r)],
                         [[sign * (q + 1), -sign, sign] if q else [sign]]))
    # Exhaust all two-gate placements on three initial wires, including
    # independent uses, throughs, branching, and seams changing dependence.
    for p, q in product(range(1, 4), repeat=2):
        for slot in range(4 - p):
            live = 3 - p + q
            for r in range(1, live + 1):
                for next_slot in range(live - r + 1):
                    seam = tuple(range(1, live)) + tuple(range(-1, -live, -1))
                    check(sample(['a'] * 3, [(slot, p, q), (next_slot, r, 2)], [seam]))
    # Two independent unary sites must simultaneously reserve four slots.
    twin = check(sample(['a', 'a'], [(0, 1, 1), (1, 1, 1)], [[]]))
    assert len(twin['antichain']) == 4
    changes = [(0, 1, 3), (1, 2, 1), (2, 1, 2), (0, 2, 2), (1, 2, 1), (0, 3, 1)]
    branch = check(sample(['a', 'a'], changes, [[1, -2], [], [-2], [2, 1], []]))
    # The triangular incidence of round-one Response 90. Joining slots 0,4
    # at the first merge requires a real middle seam with both crossing signs.
    triangle = sample(['a'] * 3, [(0, 1, 2), (2, 1, 2), (4, 1, 2),
                                 (0, 2, 1), (1, 2, 1), (2, 2, 1)],
                      [[], [], [-4, 3, -2], [], []])
    triangular = check(triangle)
    assert len(triangular['antichain']) == len(triangular['event_images']) == 6
    _, _, producers, _, trace = read_edges(triangular['movie'])
    assert [{producers[w] for w in ins} for _, ins, _, _ in trace[3:]] == [{0, 2}, {0, 1}, {1, 2}]
    print(f'{cases} signed movies decoded at their exact segment addresses and seams; '
          f'{positive} positive widths equal the independent mixed-frontier maximum.')
    print('Dependent six-event example:', len(branch['antichain']), 'strands,',
          len(branch['event_images']), 'binary uses.')
    print('Triangular incidence: six strands and six binary uses.')


def check_literal_ports():
    from catt import STAR, arr, check_ctx, comp2, infer, subst_tm, subst_ty, v
    from relative_coherence_hidden_seam import identity
    from semistrict_surface_skeletal_base import right_unit

    for rank in (2, 3):
        point = (STAR,)
        blank = v(0)
        for _ in range(rank):
            blank = identity(point, blank)
        scalar = infer(point, blank)
        old = point + (scalar,) * 4
        middle = comp2(old, rank - 1, v(2), v(3))
        old += (arr(scalar, v(1), middle), arr(scalar, middle, v(4)))
        # Three named two-lane rows, one named binary update between each.
        named = point + (scalar,) * 6
        rows = [comp2(named, rank - 1, v(i), v(i + 1)) for i in (1, 3, 5)]
        named += (arr(scalar, rows[0], rows[1]), arr(scalar, rows[1], rows[2]))
        tester = point + (scalar,)
        pair = comp2(tester, rank - 1, v(1), v(1))
        tester += (arr(scalar, pair, pair),)
        program = comp2(named, rank, v(7), v(8))
        split = comp2(old, rank, right_unit(old, v(1), rank, False), v(5))
        merge = comp2(old, rank, v(6), right_unit(old, v(4), rank, True))
        decode_images = [v(0), v(1), blank, v(2), v(3), v(4), blank, split, merge]
        fold_images = [v(0)] + [v(1)] * 6 + [v(2)] * 2
        check_ctx(named)
        for target, images in [(old, decode_images), (tester, fold_images)]:
            check_ctx(target)
            for j, term in enumerate(images):
                assert infer(target, term) == subst_ty(named[j], images[:j])
            assert infer(target, subst_tm(program, images)) == subst_ty(
                arr(scalar, rows[0], rows[-1]), images)
    print('Raw type inference checked both substitutions on a split followed by a merge at ranks 2 and 3.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, nargs='?')
    args = parser.parse_args()
    if args.input:
        print(json.dumps(encode(json.loads(args.input.read_text()))))
    else:
        audit()
        check_literal_ports()
