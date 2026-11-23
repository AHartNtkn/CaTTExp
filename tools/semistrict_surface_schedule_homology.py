"""Compare the schedule bar resolution and the cubical incidence complex on wire pairs."""
from collections import defaultdict
from itertools import combinations

from semistrict_surface_concurrent_rules import Network, subsets
from semistrict_surface_serial_detection import branching_network, refines, schedules


def frontier(net, cut, batch):
    stationary = net.cuts[cut].difference(*(net.inputs[e] for e in batch))
    return sorted(stationary | {~e for e in batch})


def expand(pair, net, before, surviving, sign):
    def blocks(w):
        if w >= 0 or ~w in surviving:
            return [w]
        return (net.outputs if ~w in before else net.inputs)[~w]
    for x in blocks(pair[0]):
        for y in blocks(pair[1]):
            assert x != y
            yield (min(x, y), max(x, y)), (1 if x < y else sign)


def add(column, target, weight):
    column[target] = column.get(target, 0) + weight
    if not column[target]:
        del column[target]


def cube(net, sign):
    levels = defaultdict(dict)
    for cut, live in net.cuts.items():
        enabled = [e for e in net.events if e not in cut and net.inputs[e] <= live]
        for batch in subsets(enabled):
            for pair in combinations(frontier(net, cut, batch), 2):
                col = {}
                for i, event in enumerate(sorted(batch)):
                    rest = batch-{event}
                    for after in (False, True):
                        end = cut | {event} if after else cut
                        for p, w in expand(pair, net, end, rest, sign):
                            add(col, (end, rest, p), (-1)**i * (1 if after else -1) * w)
                levels[len(batch)][cut, batch, pair] = col
    return levels


def schedule_bar(net, sign):
    arcs = [(e, f) for e, f in net.wires if e is not None and f is not None]
    all_s = list(schedules(frozenset(net.events), arcs))
    greater = {s: [t for t in all_s if t != s and refines(t, s)] for s in all_s}

    def chains(s):
        yield (s,)
        for t in greater[s]:
            for tail in chains(t):
                yield (s,) + tail

    def frontiers(s):
        start = frozenset()
        yield start, frozenset()
        for batch in s:
            yield start, batch
            start |= batch
            yield start, frozenset()

    levels = defaultdict(dict)
    for s in all_s:
        for chain in chains(s):
            p = len(chain)-1
            for cut, batch in frontiers(s):
                for pair in combinations(frontier(net, cut, batch), 2):
                    col = {}
                    if batch:
                        for end, orientation in ((cut, -1), (cut | batch, 1)):
                            for v, w in expand(pair, net, end, frozenset(), sign):
                                add(col, (chain, end, frozenset(), v), (-1)**p * orientation * w)
                    if p:
                        for j in range(1, p+1):
                            subchain = chain[:j] + chain[j+1:]
                            add(col, (subchain, cut, batch, pair), (-1)**j)
                        if batch:
                            for start, part in frontiers(chain[1]):
                                if part and part <= batch:
                                    for v, w in expand(pair, net, start, part, sign):
                                        add(col, (chain[1:], start, part, v), w)
                        else:
                            add(col, (chain[1:], cut, batch, pair), 1)
                    levels[p + bool(batch)][chain, cut, batch, pair] = col
    return levels


def rank_mod(columns, row_index, prime):
    pivots = {}
    for column in columns:
        v = {row_index[k]: a % prime for k, a in column.items() if a % prime}
        while v:
            i = min(v)
            if i not in pivots:
                scale = pow(v[i], -1, prime)
                pivots[i] = {k: a*scale % prime for k, a in v.items()}
                break
            scale = v[i]
            for k, a in pivots[i].items():
                v[k] = (v.get(k, 0) - scale*a) % prime
                if not v[k]:
                    del v[k]
    return len(pivots)


def check_complex(levels):
    top = max(levels)
    for d in range(2, top+1):
        for col in levels[d].values():
            composite = {}
            for row, w in col.items():
                for end, v in levels[d-1][row].items():
                    add(composite, end, w*v)
            assert not composite
    homology = []
    for prime in (2, 3, 5):
        ranks = [0]
        for d in range(1, top+1):
            rows = {k:i for i,k in enumerate(levels[d-1])}
            ranks.append(rank_mod(levels[d].values(), rows, prime))
        ranks.append(0)
        assert all(len(levels[d]) == ranks[d] + ranks[d+1] for d in range(1, top+1))
        homology.append(len(levels[0])-ranks[1])
    assert len(set(homology)) == 1
    return homology[0]


if __name__ == '__main__':
    independent = Network(3, [(None, e) for e in range(3) for _ in range(2)]
                             + [(e, None) for e in range(3) for _ in range(2)])
    branch = Network(4, [(None, 0), (None, 1), (0, 2), (1, 2), (0, 3), (1, 3),
                         (2, None), (3, None)])
    for name, net in [('independent', independent), ('branch', branch), ('six-event', branching_network())]:
        for sign in (-1, 1):
            cubical = check_complex(cube(net, sign))
            if name != 'six-event':
                bar = check_complex(schedule_bar(net, sign))
                assert bar == cubical
            print(f'{name}, sign {sign:+d}, homology concentrated in degree zero of rank {cubical}')
