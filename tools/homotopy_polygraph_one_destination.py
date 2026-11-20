"""Classify one-destination semaphore histories, including arbitrary old holdings."""

from itertools import chain, combinations, product

from homotopy_polygraph_cubical_switch import cube_chain_betti
from homotopy_polygraph_semaphore import Ring, clock_chart, histories
from homotopy_polygraph_transfer_graph import components, ordered_partitions
from homotopy_polygraph_two_resources import profiles


def endpoint_pairs(vertices, graph, resources):
    """Compute all attainable endpoint masks without bounding the walk or counts."""
    outgoing = {v: [] for v in vertices}
    for a, op, b in graph:
        outgoing[a].append((op, b))
    stack = [(v, 0, 0) for v in outgoing]
    seen = set(stack)
    supports = set()
    while stack:
        v, acquired, released = stack.pop()
        supports.add((acquired, released))
        for op, w in outgoing[v]:
            p, q = acquired, released
            if op is not None:
                kind, r = op
                bit = 1 << r
                if kind == 'P':
                    if q:
                        raise ValueError("acquisition after release")
                    p |= bit
                elif kind == 'V':
                    if p & bit or q not in (0, bit):
                        raise ValueError("incompatible release resource")
                    q = bit
                else:
                    raise ValueError(f'unknown operation {kind}')
            state = w, p, q
            if state not in seen:
                seen.add(state)
                stack.append(state)
    return {(active & ~q, active & ~p)
            for p, q in supports for active in range(1 << resources)}


def sphere_factors(axes, resources):
    """Return None for no history, otherwise the dimensions (including zero)."""
    guards = {r for r in range(resources) if not any(all(m >> r & 1 for m in axis) for axis in axes)}
    sink = resources  # unconstrained destination for processes without a guarded arrival
    arrivals = {r: set() for r in guards}
    departures = {r: set() for r in guards}
    heads = []
    for i, axis in enumerate(axes):
        ends = [r for r in guards if axis[-1] >> r & 1]
        if len(ends) > 1:
            raise ValueError("more than one guarded arrival")
        heads.append(ends[0] if ends else sink)
        for r in ends:
            arrivals[r].add(i)
        for r in guards:
            if axis[0] >> r & 1:
                departures[r].add(i)
    if any(not arrivals[r] or not departures[r] for r in guards):
        return None
    arcs = [(v, heads[i]) for v in guards for i in departures[v]]
    dimensions = []
    for part in components(arcs):
        if sink in part or any(v in part and w not in part for v, w in arcs):
            continue
        actors = set().union(*(arrivals[v] for v in part))
        internal = set().union(*(departures[v] for v in part))
        if actors == internal:
            d = len(actors) - len(part) - 1
            if d < 0:
                return None
            dimensions.append(d)
    return tuple(sorted(dimensions))


def whole_presentation(controls, resources):
    choices = []
    for vertices, graph in controls:
        choices.append(endpoint_pairs(vertices, graph, resources))
    for axes in product(*choices):
        factors = sphere_factors(axes, resources)
        if factors and max(factors) > 0:
            return False, axes
    return True, None


def polynomial(dimensions):
    if dimensions is None:
        return ()
    values = [1]
    for d in dimensions:
        shifted = [0] * d + values
        values += [0] * d
        values = [x + y for x, y in zip(values, shifted)]
    return tuple(values)


def timing_check(heads, tails, resources):
    axes = [(sum(1 << r for r in tail), 0, 1 << head) for head, tail in zip(heads, tails)]
    dims = sphere_factors(axes, resources)
    if set(heads) != set(range(resources)) or set(chain.from_iterable(tails)) != set(range(resources)):
        assert dims is None
        return
    moves = range(len(heads))
    inc = [sum(1 << i for i in moves if heads[i] == r) for r in range(resources)]
    out = [sum(1 << i for i in moves if r in tails[i]) for r in range(resources)]
    ordered = []
    for tiers in ordered_partitions((1 << len(heads)) - 1):
        def witness(r):
            first = next(j for j, t in enumerate(tiers) if t & inc[r])
            return any(t & out[r] for t in tiers[first + 1:])
        if all(witness(r) for r in range(resources)):
            ordered.append(tiers)
    assert cube_chain_betti(ordered, len(heads)) == polynomial(dims), (heads, tails)


def check():
    from homotopy_polygraph_mask_catalogue import catalogue

    graph = [(0, ('P', 0), 0), (0, ('P', 1), 1), (1, None, 1), (1, ('V', 2), 1)]
    pairs = endpoint_pairs(range(2), graph, 3)
    assert pairs == {(axis[0], axis[-1]) for axis in catalogue(range(2), graph, 3)}
    print(f'Cyclic multiple-tail control: {len(pairs)} endpoint pairs.')
    tested = 0
    for heads in ((0, 1, 2), (0, 0, 1, 2), (0, 0, 1, 1, 2)):
        def choices(head):
            other = [r for r in range(3) if r != head]
            return [*combinations(other, 1), tuple(other)]
        for tails in product(*(choices(h) for h in heads)):
            timing_check(heads, tails, 3)
            tested += 1
    print(f'{tested} multiple-tail timing systems checked by ordered partitions or endpoint exclusion.')

    # Two internal actors in each direction. A fifth arrival with no tail in the
    # component makes its punctured timing space contractible.
    pairs = [(1, 0), (1, 0), (0, 1), (0, 1)]
    programs = [(('P', t), ('V', h)) for t, h in pairs] + [(('V', 0),)]
    initial = [tuple(int(r != t) for r in (0, 1)) for t, _ in pairs] + [(1, 1)]
    states = profiles(programs, initial)
    axes = [tuple(sum(1 << r for r in (0, 1) if not counts[r]) for counts in row) for row in states]
    assert sphere_factors(axes, 2) == ()
    actual = set()
    layout = Ring(5)
    for pos in product(*(range(len(row)) for row in axes)):
        for flags in product(*(range(1 + int(t + 1 < len(row))) for row, t in zip(axes, pos))):
            moving = tuple(i for i, b in enumerate(flags) if b)
            if clock_chart(layout, programs, states, pos, moving, 2):
                actual.add((pos, moving))
    betti = histories(programs, actual)
    assert betti[0] == 1 and not any(betti[1:])
    print(f'Additional arrival: {len(actual)} spatial cubes, contractible prediction.')

    def control(word):
        return range(len(word) + 1), [(i, op, i + 1) for i, op in enumerate(word)]
    # Three one-way processes and a fixed fourth always pass. Mixed two-against-two fails.
    for words, expected in [([programs[0]]*3 + [()], True), (programs[:4], False)]:
        result, witness = whole_presentation([control(w) for w in words], 2)
        assert result == expected
        if witness:
            print('Whole-presentation failing axis record:', witness)


if __name__ == '__main__':
    check()
