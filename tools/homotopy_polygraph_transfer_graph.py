"""Decide single-transfer controls and check compressed and spatial fibres."""

from fractions import Fraction
from functools import cache
from itertools import combinations_with_replacement, product

from homotopy_polygraph_cubical_switch import cube_chain_betti, subsets
from homotopy_polygraph_two_resources import profiles
from homotopy_polygraph_semaphore import Ring, clock_chart


def components(edges):
    vertices = {v for edge in edges for v in edge}
    reach = {v: {v} for v in vertices}
    for s, t in edges:
        reach[s].add(t)
    for v in vertices:
        for s in vertices:
            if v in reach[s]:
                reach[s].update(reach[v])
    return {frozenset(w for w in reach[v] if v in reach[w]) for v in vertices}


def transfer_options(graph):
    """Recognize the control class and its achievable ordered transfers."""
    outgoing = {}
    for s, action, t in graph:
        outgoing.setdefault(s, []).append((action, t))
    # Remember the resource names. A release with a prior acquisition witnesses a transfer.
    pending = [(s, None, None) for s in outgoing]
    seen = set(pending)
    options = set()
    while pending:
        s, acquired, released = pending.pop()
        for action, t in outgoing[s]:
            p, v = acquired, released
            if action is not None:
                kind, r = action
                if kind == 'P':
                    if p not in (None, r) or v == r:
                        raise ValueError("walk uses incompatible acquisition resources")
                    p = r
                elif kind == 'V':
                    if v not in (None, r) or p == r:
                        raise ValueError("walk uses incompatible release resources")
                    v = r
                    if p is not None:
                        options.add((p, r))
                else:
                    raise ValueError(f'unknown operation {kind}')
            state = t, p, v
            if state not in seen:
                seen.add(state)
                pending.append(state)
    return options


def obstruction(graphs):
    """Return participating process indices and transfers for a failing SCC."""
    choices = [opts or {None} for opts in map(transfer_options, graphs)]
    for assignment in product(*choices):
        edges = [e for e in assignment if e is not None]
        for part in components(edges):
            inside = [(i, e) for i, e in enumerate(assignment)
                      if e is not None and set(e) <= part]
            if len(inside) >= len(part) + 2:
                return inside
    return None


@cache
def ordered_partitions(bits):
    if not bits:
        return ((),)
    return tuple((first,) + tail for first in subsets(bits) if first
                 for tail in ordered_partitions(bits ^ first))


def timing_betti(edges, guards):
    n = len(edges)
    incidences = [(sum(1 << i for i, (_, dst) in enumerate(edges) if dst == v),
                   sum(1 << i for i, (src, _) in enumerate(edges) if src == v))
                  for v in guards]
    if any(not incoming or not outgoing for incoming, outgoing in incidences):
        return ()
    def passes(tiers, incoming, outgoing):
        first = next(i for i, block in enumerate(tiers) if block & incoming)
        return any(block & outgoing for block in tiers[first + 1:])
    cells = [p for p in ordered_partitions((1 << n) - 1)
             if all(passes(p, left, right) for left, right in incidences)]
    return cube_chain_betti(cells, n)


def spatial_euler(edges):
    programs = [(('P', s), ('V', t)) for s, t in edges]
    n = len(edges)
    layout = Ring(n)
    resources = max(max(e) for e in edges) + 1
    states = profiles(programs, [tuple(int(r != s) for r in range(resources)) for s, _ in edges])
    values = {(0,) * n: 1}
    legal_cubes = 0
    for pos in product(range(3), repeat=n):
        for flags in product(*(range(1 + int(x < 2)) for x in pos)):
            moving = tuple(i for i, bit in enumerate(flags) if bit)
            if clock_chart(layout, programs, states, pos, moving, resources):
                legal_cubes += 1
                if moving:
                    target = tuple(x + b for x, b in zip(pos, flags))
                    values[target] = values.get(target, 0) + (-1) ** (len(moving) - 1) * values.get(pos, 0)
    return legal_cubes, values.get((2,) * n, 0)


def potential_section(edges, times):
    """Construct strict times from a mean-balanced, nonconstant representative."""
    vertices = sorted(set().union(*edges))
    potential = {v: Fraction(0) for v in vertices}
    strict_counts = []
    for _ in range(len(vertices) + 1):
        increments = {}
        for v in vertices:
            out = max(t + potential[b] for (a, b), t in zip(edges, times) if a == v)
            inc = min(t - potential[a] for (a, b), t in zip(edges, times) if b == v)
            increments[v] = (out - inc - 2 * potential[v]) / 4
        assert min(increments.values()) >= 0
        strict_counts.append(sum(d > 0 for d in increments.values()))
        if strict_counts[-1] == len(vertices):
            return strict_counts
        for v in vertices:
            potential[v] += increments[v]
    raise AssertionError("strict inequalities did not propagate")


def check():
    arcs = tuple((s, t) for s in range(3) for t in range(3) if s != t)
    tested = 0
    for n in range(2, 6):
        for edges in combinations_with_replacement(arcs, n):
            vertices = set().union(*edges)
            if components(edges) != {frozenset(vertices)}:
                continue
            d = n - len(vertices) - 1
            expected = () if d < 0 else (2,) if d == 0 else (1,) + (0,) * (d - 1) + (1,)
            assert timing_betti(edges, vertices) == expected, edges
            assert timing_betti(edges, vertices - {min(vertices)}) == (1,), edges
            tested += 1
    print(f'{tested} strongly connected directed multigraphs, each with full and partial guards.')
    # A non-strong weak component: each tested guard has an arrival and departure.
    bridge = [(0, 1), (1, 0), (1, 2), (2, 3), (3, 2)]
    assert timing_betti(bridge, range(4)) == (1,)
    cycle = [(0, 1), (0, 1), (1, 2), (1, 2), (2, 0)]
    def graph(s, t):
        return [(0, ('P', s), 0), (0, None, 1), (1, ('V', t), 1)]
    controls = [graph(*e) for e in cycle]
    assert len(obstruction(controls)) == 5
    for i in range(5):
        assert obstruction(controls[:i] + controls[i + 1:]) is None
    # Two length-nine cycles coincide except on the doubled first edge.
    # Their sum is a positive circulation. The difference has weighted mean
    # zero at each vertex and leaves seven vertices initially tied.
    long_cycle = [(i, (i + 1) % 9) for i in range(9)] + [(0, 1)]
    times = [1] + [0] * 8 + [-1]
    counts = potential_section(long_cycle, times)
    assert counts == [2, 4, 6, 8, 9]
    print('Strict resource inequalities after successive potential updates:', counts)
    legal, euler = spatial_euler(cycle)
    assert euler == 0 and timing_betti(cycle, range(3)) == (1, 1)
    print(f'Five-process three-resource obstruction: {legal} spatial cubes, Euler {euler}, Betti (1, 1).')


if __name__ == '__main__':
    check()
