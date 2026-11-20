"""Localize the two RC hypotheses in the six-cube sweep by vertex colours."""
from collections import Counter

from gray_globe_comparison import close_atoms
from relative_coherence_facet_sweeps import closure
from relative_coherence_ridge_exchanges import delta, forks, step
from relative_coherence_simplex_carrier import flags
from relative_coherence_steiner_cuts import tableau
from relative_coherence_sweep_colours import mask, priority_colours, sweep_rows, vertex_mask


def inventory():
    rows = sweep_rows()
    states = {}
    edges = set()
    for row in rows:
        for state, enabled in forks(row):
            source = vertex_mask(state)
            assert states.setdefault(source, state) == state
            for ridge in enabled:
                target = frozenset(step(Counter(state), delta(ridge)))
                edges.add((source, vertex_mask(target)))
    vertices = sorted(states)
    assert len(vertices) == 148 and len(edges) == 264
    index = {m: i for i, m in enumerate(vertices)}
    carriers = [(m, 1 << index[m]) for m in vertices]
    unions = [(a | b, 1 << index[a] | 1 << index[b]) for a, b in edges]
    return [states[m] for m in vertices], carriers, unions


def required(carriers, includes):
    result = 0
    for m, indices in carriers:
        if includes(m):
            result |= indices
    return result


def minimal(choices):
    return {m for m in choices if not any(n != m and n & m == n for n in choices)}


def lower_bound(carriers, limit):
    # Every triangulation must contribute a rainbow flag to a nonzero degree.
    candidates = {0}
    for origin in range(32):
        flags_needed = set()
        for flag, _ in flags(range(6)):
            vertices = mask(x ^ origin for x in flag)
            needed = required(carriers, lambda m: not vertices & ~m)
            if needed.bit_count() <= limit:
                flags_needed.add(needed)
        choices = minimal(flags_needed)
        candidates = minimal({a | b for a in candidates for b in choices
                              if (a | b).bit_count() <= limit})
        if not candidates:
            return origin + 1
    raise AssertionError("triangulations did not exclude this bound")


def label_count(state, colours):
    faces = closure(state)
    names = {face: mask(i for i, c in enumerate(colours) if vertex_mask([face]) & c)
             for face in faces}
    cells = close_atoms((tableau(face) for face in faces), 3)
    full = 0
    for rows in cells:
        support = 0
        for row in rows:
            for chain in row:
                for face in chain:
                    support |= names[face]
        full += support == 127
    return full, len(cells)


def main():
    states, carriers, unions = inventory()
    positive = [mask(x for x in range(64) if x >> j & 1) for j in range(6)]
    colours = priority_colours(5, (0, 1, 2, 3, 5, 4), positive)
    def full(m):
        return all(m & c for c in colours)
    three = required(unions, full)
    four = required(carriers, full)
    assert (three.bit_count(), four.bit_count()) == (28, 19) and four & ~three == 0
    for name, selection in (("RC(3)", three), ("RC(4)", four)):
        print(f"{name} state indices: {[i for i in range(148) if selection >> i & 1]}")
    bounds = [lower_bound(unions, 27), lower_bound(carriers, 18)]
    print(f"Lower bounds certified by {bounds[0]} and {bounds[1]} staircase triangulations.")
    selected = [label_count(s, colours) for i, s in enumerate(states) if four >> i & 1]
    print(f"Full-colour strict 3-labels in the 19 states: {sum(n for n, _ in selected)} "
          f"of {sum(t for _, t in selected)}, counted by state.")
    print(f"Per state, in order: {[n for n, _ in selected]}")


if __name__ == "__main__":
    main()
