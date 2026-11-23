"""Check serial configuration detection, schedule fibres, and incompatible cut characters."""
from argparse import ArgumentParser
from itertools import combinations, permutations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_concurrent_rules import Network, subsets
from semistrict_surface_exact_boundary import accepted, rejected, run


def check_orders():
    events = range(4)
    orders = list(permutations(events))
    sortable = obstructed = 0
    for arcs in subsets(combinations(events, 2)):
        le = {(e, e) for e in events} | arcs
        for k in events:
            le |= {(i, j) for i, j in product(events, repeat=2) if (i, k) in le and (k, j) in le}
        extensions = [order for order in orders if all(order.index(i) < order.index(j) for i, j in arcs)]
        for multi_out, multi_in in product(subsets(events), repeat=2):
            demands = [(f, m) for f, m in product(multi_out, multi_in)
                       if (f, m) not in le and (m, f) not in le]
            success = any(all(order.index(f) < order.index(m) for f, m in demands)
                          for order in extensions)
            opposed = any((m, g) in le and (n, f) in le
                          for (f, m), (g, n) in combinations(demands, 2))
            assert success != opposed
            sortable += success
            obstructed += opposed
    return sortable, obstructed


def schedules(events, arcs):
    if not events:
        yield ()
        return
    enabled = events - {b for a, b in arcs if a in events}
    for batch in subsets(enabled):
        if batch:
            for tail in schedules(events-batch, arcs):
                yield (batch,) + tail


def refines(fine, coarse):
    if not fine:
        return not coarse
    end = 0
    for block in coarse:
        start = end
        while end < len(fine) and fine[end] <= block:
            end += 1
        if start == end or frozenset.union(*fine[start:end]) != block:
            return False
    return end == len(fine)


def check_fibres():
    """Compute the actual upper fibres for deletion at every minimal event."""
    events = frozenset(range(4))
    tests = longest = 0
    for arcs in subsets(combinations(events, 2)):
        whole = list(schedules(events, arcs))
        for t in events - {b for _, b in arcs}:
            fibres = {}
            for s in whole:
                base = tuple(batch-{t} for batch in s if batch != {t})
                fibres.setdefault(base, []).append(s)
            for base, lifts in fibres.items():
                for coarse_base in fibres:
                    if not refines(base, coarse_base):
                        continue
                    for coarse in fibres[coarse_base]:
                        choices = [s for s in lifts if refines(s, coarse)]
                        # A gap has an even position and a joined batch an odd one.
                        positions = sorted(2*i + int(batch != {t}) for s in choices
                                           for i, batch in enumerate(s) if t in batch)
                        assert positions and positions == list(range(positions[0], positions[-1]+1))
                        for first, second in combinations(choices, 2):
                            i = next(i for i,b in enumerate(first) if t in b)
                            j = next(j for j,b in enumerate(second) if t in b)
                            adjacent = abs((2*i + int(first[i] != {t}))
                                           - (2*j + int(second[j] != {t}))) == 1
                            assert (refines(first, second) or refines(second, first)) == adjacent
                        longest = max(longest, len(positions))
                        tests += 1
    return tests, longest


def flow(net, event, forward):
    # Two opposite unit flows born at outputs or ending at inputs.
    ins, outs = (net.inputs, net.outputs) if forward else (net.outputs, net.inputs)
    values = [0]*len(net.wires)
    first, second = sorted(outs[event])[:2]
    values[first], values[second] = 1, -1
    order = range(event+1, len(net.events)) if forward else range(event-1, -1, -1)
    for e in order:
        values[min(outs[e])] = sum(values[w] for w in ins[e])
    for i, o in zip(ins, outs):
        assert sum(values[w] for w in i) == sum(values[w] for w in o)
    return values


def check_characters(net, demands, sign):
    profiles = [(flow(net, f, True), flow(net, m, False)) for f, m in demands]

    def pair_value(u, v, rows):
        left, right = rows
        return (sum(left[w] for w in u)*sum(right[w] for w in v)
                + sign*sum(right[w] for w in u)*sum(left[w] for w in v))

    supports = [set(), set()]
    edge_values = 0
    for c, live in net.cuts.items():
        for k, ((f, m), rows) in enumerate(zip(demands, profiles)):
            values = [pair_value([v], [w], rows) for v, w in combinations(live, 2)]
            if any(values):
                assert f in c and m not in c
                if any(abs(x) == 1 for x in values):
                    supports[k].add(c)
            for e in net.events:
                if e in c or c | {e} not in net.cuts:
                    continue
                stationary = live - net.inputs[e]
                sides = [[{w} for w in sorted(stationary)] + [ports]
                         for ports in (net.inputs[e], net.outputs[e])]
                images = [[pair_value(u, v, rows) for u, v in combinations(side, 2)]
                          for side in sides]
                assert images[0] == images[1]
                edge_values += len(images[0])
    assert all(supports)
    assert all(not (c <= d or d <= c) for c, d in product(*supports))
    return edge_values


def branching_network():
    pairs = list(combinations(range(3), 2))
    wires = [(None, e) for e in range(3)]
    wires += [(e, 3+i) for e, pair in enumerate(pairs) for i in pair]
    wires += [(3+i, None) for i in range(3)]
    return Network(6, wires)


def check_central_cut():
    net = branching_network()
    centre = frozenset(range(3))
    blocks = net.blocks(centre)
    assert len(net.cuts[centre]) == 6
    for c, live in net.cuts.items():
        partition = [blocks[w] for w in live]
        assert set.union(*partition) == net.cuts[centre]
        assert sum(map(len, partition)) == 6
        # Every off-centre cut has a legal move expanding a unary side.
        if c != centre:
            assert (any(c | {e} in net.cuts and len(net.inputs[e]) == 1 for e in centre-c)
                    or any(c-{e} in net.cuts and len(net.outputs[e]) == 1 for e in c-centre))
    return len(net.cuts)


def check_rice(checkout):
    context = '(x : *)' + ''.join(f' ({w} : id(id(x)) -> id(id(x)))' for w in 'abcdefghijkl')
    context += ' (p : a -> comp[d,e]) (q : b -> comp[f,g]) (r : c -> comp[h,i])'
    context += ' (s : comp[e,f] -> j) (t : comp[g,h] -> k) (u : comp[i,d] -> l)'
    route = 'route(x,a,b,c,d,e,f,g,h,i,j,k,l,p,q,r,s,t,u)'
    base = '''import examples/eh
def open_first = coh [ [a,b,c,d,e,f] : comp[comp[a,b],comp[c,d],comp[e,f]] -> comp[a,comp[b,c,d,e,f]] ]
def close_last = coh [ [a,b,c,d,e,f] : comp[comp[a,b,c,d,e],f] -> comp[comp[a,b],comp[c,d],comp[e,f]] ]
'''
    base += (f'def route {context} : comp[a,b,c] -> comp[j,k,l] = '
             'comp[comp[[p],[q],[r]],open_first(d,e,f,g,h,i),eh(id(x),d,comp[e,f,g,h,i]),'
             'close_last(e,f,g,h,i,d),comp[[s],[t],[u]]]\n')
    # Test the same literal 6-type at the twice-iterated end of the four-dimensional route.
    face = f'id({route})'
    boundary = f'comp[{face},id({route})] -> {face}'
    exe = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        for name, term in [('Unitor', f'unitor_r({face})'), ('Convert', f'id({face})')]:
            file = name + '.catt'
            (folder / file).write_text(base + f'def fill {context} : {boundary} = {term}\n')
            for flags in ([], ['--sua']):
                result = run(exe, folder, file, flags)
                if not flags and name == 'Convert':
                    rejected(result, file, 'fill')
                else:
                    accepted(result, file, ['route', 'fill'])


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    print('Sortable and obstructed four-event inputs:', *check_orders())
    print('Deletion fibres checked and largest interval:', *check_fibres())
    square = Network(2, [(None, 0), (None, 0), (0, None), (0, None),
                         (None, 1), (None, 1), (1, None), (1, None)])
    # The incompatible windows here involve four distinct events. Flow passes
    # through a predecessor and a successor outside the two core chains.
    chains = Network(6, [(None, 0), (0, 1), (0, 2), (None, 1), (None, 2),
                         (1, 3), (2, 4), (3, 5), (4, 5), (3, None), (4, None), (5, None)])
    for sign in (-1, 1):
        print(f'Character incidence values at sign {sign:+d}:',
              check_characters(square, [(0, 1), (1, 0)], sign),
              check_characters(chains, [(3, 2), (4, 1)], sign))
    print('Cuts expanding to the six middle wires, including the middle cut:', check_central_cut())
    if args.catt_strict:
        check_rice(args.catt_strict.resolve())
        print('Checked the six-event route and the raw and SUA fillers at its old 6-type.')
