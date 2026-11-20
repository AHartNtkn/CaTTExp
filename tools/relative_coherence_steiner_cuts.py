"""Recover strict tableaux from independent lower-dimensional directed cuts."""
from collections import Counter, defaultdict
from functools import cache
from itertools import product

from gray_globe_comparison import close_atoms
from relative_coherence_facet_sweeps import closure, differential
from relative_coherence_ridge_exchanges import forks, membranes


def poles(face):
    return (tuple(v or -1 for v in face), tuple(v or 1 for v in face))


@cache
def tableau(face):
    sides = []
    for sign in (-1, 1):
        row = Counter([face])
        rows = []
        while row:
            rows.append(tuple(sorted(row.elements())))
            change = differential(row)
            row = -change if sign < 0 else +change
        sides.append(rows[::-1])
    return tuple(zip(*sides))


def restrict(rows, kept):
    return tuple(tuple(tuple(f for f in chain if f in kept) for chain in row) for row in rows)


def cut_atoms(kept):
    result = []
    for face in kept:
        sides = []
        for sign in (-1, 1):
            row = Counter([face])
            rows = []
            for _ in range(face.count(0)):
                rows.append(tuple(sorted(row.elements())))
                change = differential(row)
                row = Counter({g: sign * n for g, n in change.items() if g in kept and sign * n > 0})
            assert len(rows[-1]) == 1
            sides.append(rows[::-1])
        cell = tuple(zip(*sides))
        assert cell == restrict(tableau(face)[1:], kept)
        result.append(cell)
    return result


def match_counts(faces, degree, verify=False):
    vertices = sorted(f for f in faces if 0 not in f)
    index = {v: i for i, v in enumerate(vertices)}
    spans = {f: tuple(index[v] for v in poles(f)) for f in faces if 0 in f}
    layers = [{f for f, (s, t) in spans.items() if s < j <= t} for j in range(1, len(vertices))]
    choices = [close_atoms(cut_atoms(layer), degree - 1) for layer in layers]
    zero = (((), ()),) * degree
    # Free endpoints: include the zero section in every layer; allow a
    # nonzero interval to start and end only once. Accumulate matching counts.
    active = Counter({(False, zero): 1})
    previous = set()
    finished = 0
    for layer, local in zip(layers, choices):
        common = previous & layer
        weights = Counter()
        for (started, rows), count in active.items():
            weights[started, restrict(rows, common)] += count
        current = Counter()
        current[False, zero] = 1
        for rows in local:
            key = restrict(rows, common)
            current[True, rows] = weights[False, key] + weights[True, key]
        finished += weights[True, zero]
        active, previous = current, layer
    finished += sum(count for (started, _), count in active.items() if started)
    total = len(vertices) + finished
    if verify:
        global_cells = close_atoms((tableau(f) for f in faces), degree)
        assert len(global_cells) == total
        # Compare actual tuples as well as the count, including the two poles.
        grouped = defaultdict(set)
        for rows in global_cells:
            p, q = (index[chain[0]] for chain in rows[0])
            key = tuple(restrict(rows[1:], layer) for layer in layers)
            assert key not in grouped[p, q]
            grouped[p, q].add(key)
            for j, entry in enumerate(key, 1):
                assert entry in (choices[j - 1] if p < j <= q else {zero})
    return total, max(map(len, choices))


def main():
    for dimension in (2, 3, 4):
        faces = set(product((-1, 0, 1), repeat=dimension))
        answer = [match_counts(faces, n, True)[0] for n in range(1, dimension + 1)]
        print(f"Full {dimension}-cube: levels 1 through {dimension}: {answer}.")
    states = {r for membrane in membranes() for r, _ in forks(membrane)}
    totals = Counter()
    largest = 0
    for state in sorted(states, key=lambda s: sorted(s)):
        count, size = match_counts(closure(state), 3)
        largest = max(largest, size)
        totals[count] += 1
    assert len(states) == 148
    print(f"148 states: strict 3-cell counts {min(totals)}..{max(totals)},"
          f" {len(totals)} distinct totals, sum {sum(count * frequency for count, frequency in totals.items())};"
          f" largest local 2-cell table {largest}.")


if __name__ == '__main__':
    main()
