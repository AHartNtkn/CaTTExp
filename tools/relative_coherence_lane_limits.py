"""Compare the strict matching object of lane histories with the ring fibre."""
from collections import defaultdict
from graphlib import CycleError, TopologicalSorter
from itertools import combinations

from relative_coherence_spherical_fibres import ring
from relative_coherence_strip_fibres import Complex, project, restrict_rules


def lane_complex(data, lanes):
    initial, final, rules, typed = data

    def valid(tier):
        padded = list(initial)
        for i, word in zip(lanes, tier):
            padded[i] = word
        return typed(padded)

    return Complex(tuple(initial[i] for i in lanes), tuple(final[i] for i in lanes),
                   restrict_rules(rules, lanes), valid)


def restrict(cell, domain, target):
    return project(cell, [domain.index(i) for i in target])


def match(proper, domains):
    # Natural join of independently generated local tables. Compare cells on
    # intersections *after* dropping tiers that became empty there.
    families = [()]
    for j, domain in enumerate(domains):
        overlaps = [tuple(i for i in domain if i in old) for old in domains[:j]]
        by_views = defaultdict(list)
        for value in proper[domain].cells:
            key = tuple(restrict(value, domain, overlap) for overlap in overlaps)
            by_views[key].append(value)
        families = [prefix + (value,) for prefix in families
                    for value in by_views[tuple(restrict(old, old_domain, overlap)
                                                for old, old_domain, overlap
                                                in zip(prefix, domains, overlaps))]]
    return set(families)


def check_limits(data, expected_betti):
    lanes = tuple(range(len(data[0])))
    spaces = {subset: lane_complex(data, subset) for n in range(len(lanes) + 1)
              for subset in combinations(lanes, n)}
    whole = spaces[lanes]
    for subset, space in spaces.items():
        if subset == lanes:
            continue
        if len(whole.components) == 1:
            assert len(space.components) == 1 and space.betti(space.components[0]) == (1,)
        else:
            assert all(space.betti(component) == (1,) for component in space.components)
    domains = list(combinations(lanes, len(lanes) - 1))
    joined = match(spaces, domains)
    views = [tuple(restrict(cell, lanes, d) for d in domains) for cell in whole.cells]
    assert len(set(views)) == len(whole.cells) and set(views) == joined
    # Test order reflection as well as reconstruction of the underlying set.
    ideals = [{cell: obj.ideal(i) for i, cell in enumerate(obj.cells)}
              for obj in (spaces[d] for d in domains)]
    for row_id, row in enumerate(views):
        expected = whole.ideal(row_id)
        observed = {i for i, other in enumerate(views)
                    if all(spaces[d].index[v] in ideal[w] for d, v, w, ideal
                           in zip(domains, other, row, ideals))}
        assert observed == expected
    assert sorted(whole.betti(c) for c in whole.components) == expected_betti
    print(f"{len(spaces)-1} proper lane selections, {len(joined)} matching families,"
          f" {len(joined)**2} order tests, full component Betti numbers {expected_betti}.")


def check_orders(k):
    # Extract temporal edges from the typed signal rewrites by matching the
    # output gate of one event to the input gate of the other.
    initial, _, rules, _ = ring(k)
    signal = {}
    for i in range(0, len(initial), 2):
        changes = {name: faces[i] for name, faces in rules.items()
                   if i in faces and faces[i][0] != faces[i][1]}
        a, b = (name for name in changes)
        if changes[b][1] == changes[a][0]:
            a, b = b, a
        assert changes[a][1] == changes[b][0]
        signal[i] = (a, b)
    seams = {}
    for i in range(1, len(initial), 2):
        a, = (name for name, faces in rules.items() if faces.get(i) == ('d', ''))
        b, = (name for name, faces in rules.items() if faces.get(i) == ('', 'e'))
        seams[i] = (a, b)
    edges = signal | seams
    total = 0
    for n in range(len(initial) + 1):
        for lanes in combinations(range(len(initial)), n):
            graph = TopologicalSorter()
            for i in lanes:
                a, b = edges[i]
                graph.add(b, a)
            try:
                tuple(graph.static_order())
                feasible = True
            except CycleError:
                feasible = False
            assert feasible == (n < len(initial))
            total += 1
    print(f"{k} seams: all-hidden order tested on {total} lane selections.")


if __name__ == '__main__':
    data = ring(2)
    check_limits(data, [(1, 1)])
    initial, final, rules, typed = data
    check_limits((('l', 'tdd') + initial[2:], ('r', 'tde') + final[2:], rules, typed),
                 [(1,), (1, 1)])
    check_orders(6)
