"""Check the free enriched extension filtration for the rewrite a : f => ff."""

from collections import Counter, defaultdict
from itertools import combinations, permutations
from math import factorial

from gray_globe_comparison import atom


def paths(edges, remaining, used=(), positions=()):
    """Enumerate unrestricted rewrites, retaining the ancestry of each edge."""
    if remaining == 0:
        yield used, positions
        return
    for i, edge in enumerate(edges):
        children = (edge + (0,), edge + (1,))
        yield from paths(edges[:i] + children + edges[i + 1:], remaining - 1,
                         used + (edge,), positions + (i,))


def cube_path(selected, order):
    done = []
    result = []
    for event in order:
        position = selected[event]
        result.append(position + sum(selected[j] < position for j in done))
        done.append(event)
    return tuple(result)


def cube_faces(swaps):
    events = [2, 1, 0]
    faces = []
    for at in swaps:
        fixed = events[2] if at == 0 else events[0]
        faces.append(tuple((0, int(at == 1)) if j == fixed else (1, 2) for j in range(3)))
        events[at], events[at + 1] = events[at + 1], events[at]
    assert events == [0, 1, 2]
    return tuple(sorted(faces))


def check():
    counts = Counter()
    for n in range(1, 7):
        edges = tuple((i,) for i in range(n))
        for r in range(1, 5):
            independent = defaultdict(set)
            for used, pos in paths(edges, r):
                counts["rewrite paths"] += 1
                if all(len(edge) == 1 for edge in used):
                    key = tuple(sorted(edge[0] for edge in used))
                    independent[key].add(pos)
                else:
                    counts["paths using an output edge"] += 1

            # One old f-word in each of the r+1 gaps, and one interval in
            # each of the r occupied positions. Compare all its executions.
            expected = set(combinations(range(n), r))
            assert independent.keys() == expected
            for selected in expected:
                executions = {cube_path(selected, order) for order in permutations(range(r))}
                assert len(executions) == factorial(r)
                assert independent[selected] == executions
                counts["cube charts"] += 1
                counts["independent executions"] += len(executions)

    # A directed 3-cube separates the two square-pastes on the six orders.
    before, after = atom(((1, 2),) * 3)[2]
    first, second = cube_faces((0, 1, 0)), cube_faces((1, 0, 1))
    assert before != after and {before, after} == {first, second}
    for kind, count in sorted(counts.items()):
        print(f"{count:,} {kind}")
    print("Both boundaries of the tensor 3-cell match the two different square-pastes.")


if __name__ == "__main__":
    check()
