"""Classify the allowed full-colour membranes for degree on the six-cube boundary."""
from collections import Counter
from itertools import permutations

from relative_coherence_facet_sweeps import closure, differential
from relative_coherence_ridge_exchanges import delta, forks, step
from relative_coherence_simplex_carrier import flags


def mask(indices):
    return sum(1 << i for i in indices)


def vertex_mask(row):
    return mask(mask(i for i, sign in enumerate(face) if sign == 1)
                for face in closure(row) if 0 not in face)


def sweep_rows():
    sides = delta((0,) * 6)
    initial = -differential(-sides)
    walks = []
    for side in (-sides, +sides):
        row, remaining = initial, set(side)
        walk = [frozenset(row)]
        while remaining:
            face, = [f for f in remaining if -delta(f) <= row]
            row = step(row, delta(face))
            walk.append(frozenset(row))
            remaining.remove(face)
        walks.append(walk)
    assert walks[0][0] == walks[1][0] and walks[0][-1] == walks[1][-1]
    return walks[0] + walks[1][-2:0:-1]


def priority_colours(seed, order, positive_facets):
    unused = (1 << 64) - 1
    colours = []
    for axis in order:
        differs = positive_facets[axis]
        if seed >> axis & 1:
            differs = ~differs
        colours.append(unused & differs)
        unused &= ~differs
    return [unused, *colours]


def main():
    axes = range(6)
    rows = sweep_rows()
    carriers = [vertex_mask(row) for row in rows]
    assert len(set(carriers)) == 12 and all(m.bit_count() == 57 for m in carriers)
    positive = [mask(x for x in range(64) if x >> j & 1) for j in axes]
    windows = [mask((start + j) % 12 for j in range(4)) for start in range(12)]
    witnesses, counts = {}, Counter()
    for seed in range(64):
        for order in permutations(axes):
            colours = priority_colours(seed, order, positive)
            active = mask(i for i, m in enumerate(carriers) if all(c & m for c in colours))
            counts[active.bit_count()] += 1
            witnesses.setdefault(active, (seed, order))
    assert all(block in witnesses for block in windows)
    assert all(any(block & active == block for block in windows) for active in witnesses)

    # An antipodal pair of origins gives the same unoriented staircase triangulation.
    flags_from_zero = [p for p, _ in flags(axes)]
    triangulations = []
    for origin in range(32):
        covers = set()
        for flag in flags_from_zero:
            vertices = mask(v ^ origin for v in flag)
            covers.add(mask(i for i, m in enumerate(carriers) if vertices & ~m == 0))
        triangulations.append(covers)
    positive_count = 0
    all_rows = (1 << 12) - 1
    for permitted in range(all_rows + 1):
        feasible = any(block & permitted == block for block in windows)
        outside = all_rows ^ permitted
        contracts = any(all(m & outside for m in covers) for covers in triangulations)
        assert feasible != contracts
        positive_count += feasible

    states = [{state for state, _ in forks(row)} for row in rows]
    sizes = [len(set.union(*(states[i] for i in range(12) if block >> i & 1)))
             for block in windows]
    assert min(sizes) == 57 and len(set.union(*states)) == 148
    print(f"46,080 signed priority colourings, by number of full membranes: {dict(sorted(counts.items()))}.")
    print(f"All 4,096 permissions classified: {positive_count} feasible, "
          f"{4096-positive_count} contract by a translated staircase triangulation.")
    print("Start : seed, priority axes (zero-based), number of incident states")
    for i, block in enumerate(windows):
        seed, order = witnesses[block]
        print(f"{i:2} : {seed:2}, {order}, {sizes[i]}")


if __name__ == "__main__":
    main()
