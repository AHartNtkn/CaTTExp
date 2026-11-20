"""Localize strict labels across states and compute the signed-priority hitting number."""
from collections import Counter
from functools import cache
from itertools import permutations, product

from relative_coherence_state_colours import (
    close_atoms, closure, inventory, mask, minimal, priority_colours, tableau, vertex_mask,
)


def support_profile(states, carriers, colours):
    faces = list(product((-1, 0, 1), repeat=6))
    index = {face: i for i, face in enumerate(faces)}
    closed = {f: mask(index[g] for g in closure([f])) for f in faces}
    colour_faces = [mask(index[f] for f in faces if 0 not in f and vertex_mask([f]) & c)
                    for c in colours]
    labels = {}
    occurrences = Counter()
    for state, (vertices, _) in zip(states, carriers):
        if not all(vertices & c for c in colours):
            continue
        for rows in close_atoms((tableau(f) for f in closure(state)), 3):
            support = 0
            for row in rows:
                for side in row:
                    for f in side:
                        support |= closed[f]
            if all(support & c for c in colour_faces):
                # Compare the complete strict tableaux, including their ordered boundaries.
                assert labels.setdefault(support, rows) == rows
                rank = max(j for j, (a, b) in enumerate(rows) if a or b)
                occurrences[rank] += 1
    distinct = Counter(max(j for j, (a, b) in enumerate(rows) if a or b)
                       for rows in labels.values())
    assert occurrences == {1: 19, 2: 18129, 3: 123161}
    assert distinct == {1: 1, 2: 2749, 3: 56233}
    print('Occurrences by support dimension:', dict(sorted(occurrences.items())))
    print('Distinct strict labels by support dimension:', dict(sorted(distinct.items())))


def priority_constraints(carriers, positive):
    @cache
    def meets(vertices):
        return mask(i for i, (v, _) in enumerate(carriers) if vertices & v)

    choices = {}
    for seed in range(64):
        for order in permutations(range(6)):
            full = (1 << len(carriers)) - 1
            for c in priority_colours(seed, order, positive):
                full &= meets(c)
            choices.setdefault(full, (seed, order))
    constraints = sorted(minimal(choices), key=lambda m: (m.bit_count(), m))
    assert (len(choices), len(constraints)) == (475, 72)
    return constraints, choices


def hitting_number(constraints, state_count):
    # Take disjoint constraints for a lower bound at each search node.
    packing, used = 0, 0
    for j, c in enumerate(constraints):
        if not used & c:
            used |= c
            packing |= 1 << j
    columns = [mask(j for j, c in enumerate(constraints) if c >> i & 1)
               for i in range(state_count)]
    options = [[i for i in range(state_count) if c >> i & 1] for c in constraints]

    @cache
    def hit(unmet, budget):
        if not unmet:
            return ()
        if not budget or (unmet & packing).bit_count() > budget:
            return None
        j = (unmet & -unmet).bit_length() - 1
        for i in sorted(options[j], key=lambda i: -(columns[i] & unmet).bit_count()):
            rest = hit(unmet & ~columns[i], budget - 1)
            if rest is not None:
                return (i, *rest)
        return None

    all_constraints = (1 << len(constraints)) - 1
    for size in range(packing.bit_count(), state_count + 1):
        result = hit(all_constraints, size)
        if result is not None:
            return result
    raise AssertionError('a required state set is empty')


def main():
    states, carriers, _ = inventory()
    positive = [mask(i for i in range(64) if i >> j & 1) for j in range(6)]
    constraints, choices = priority_constraints(carriers, positive)
    witness = hitting_number(constraints, len(states))
    assert len(witness) == 7 and all(m & mask(witness) for m in choices)
    print('Priority colourings: 46,080; distinct full-state sets: 475; minimal sets: 72.')
    print('Minimum number of states meeting every set:', len(witness), sorted(witness))
    support_profile(states, carriers, priority_colours(5, (0, 1, 2, 3, 5, 4), positive))


if __name__ == '__main__':
    main()
