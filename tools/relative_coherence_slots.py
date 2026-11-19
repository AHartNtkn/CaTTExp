"""Check the two pasting-shape lemmas in the higher-bubble obstruction.

Run with python3 tools/relative_coherence_slots.py [max_tree_edges].
"""

import argparse
from collections import Counter, defaultdict, deque
from functools import cache

from partial_cylinder_steiner import globular, trees


def components(vertices, pairs):
    parent = {vertex: vertex for vertex in vertices}

    def root(vertex):
        while vertex != parent[vertex]:
            vertex = parent[vertex]
        return vertex

    for left, right in pairs:
        parent[root(left)] = root(right)
    return {vertex: root(vertex) for vertex in vertices}


def transport_slots(cells, level):
    """Quotient parallel transport arrows by the equations from (level+2)-cells."""
    nodes = [x for x, (d, _, _) in cells.items() if d == level]
    arrows = [x for x, (d, _, _) in cells.items() if d == level + 1]
    equations = [(s, t) for d, s, t in cells.values() if d == level + 2]
    classes = components(arrows, equations)
    slots = components(nodes, [cells[x][1:] for x in arrows])

    incoming, outgoing = Counter(), Counter()
    for arrow in arrows:
        assert cells[arrow][1:] == cells[classes[arrow]][1:]
    for arrow in set(classes.values()):
        _, source, target = cells[arrow]
        outgoing[source] += 1
        incoming[target] += 1
    # A finite graph is a disjoint union of directed paths (points allowed)
    # under these degree bounds and the forest edge count.
    assert all(count == 1 for count in (*incoming.values(), *outgoing.values()))
    assert len(nodes) - len(set(classes.values())) == len(set(slots.values()))
    return slots


def tableaux(cells, level):
    """Close the atomic Steiner tableaux under all dimension-level compositions."""
    @cache
    def atom(x):
        degree, source, target = cells[x]
        lower = ()
        if degree:
            lower = tuple((s[0], t[1]) for s, t in zip(atom(source), atom(target)))
        return lower + (((x,), (x,)),)

    seen = {atom(x) + (((), ()),) * (level - d)
            for x, (d, _, _) in cells.items() if d <= level}
    pending = deque(seen)
    by_source, by_target = defaultdict(list), defaultdict(list)

    def join(left, right, cut):
        # Rows above the cut add as multisets. Keep repeated occurrences.
        upper = tuple((tuple(sorted(s + u)), tuple(sorted(t + v)))
                      for (s, t), (u, v) in zip(left[cut + 1:], right[cut + 1:]))
        cell = left[:cut] + ((left[cut][0], right[cut][1]),) + upper
        if cell not in seen:
            seen.add(cell)
            pending.append(cell)

    while pending:
        cell = pending.popleft()
        yield cell
        for cut in range(level):
            if not any(s or t for s, t in cell[cut + 1:]):
                continue  # a unit at this cut
            source = (cut, cell[:cut], cell[cut][0])
            target = (cut, cell[:cut], cell[cut][1])
            for left in by_target[source]:
                join(left, cell, cut)
            for right in by_source[target]:
                join(cell, right, cut)
            by_source[source].append(cell)
            by_target[target].append(cell)


def check(max_edges):
    shapes = checked_cells = 0
    for edges in range(max_edges + 1):
        for tree in trees(edges):
            shapes += 1
            cells = {x: (d, s, t) for x, d, s, t in globular(tree)}
            for level in range(1 + max(d for d, _, _ in cells.values())):
                slots = transport_slots(cells, level)
                for cell in tableaux(cells, level):
                    occurrences = cell[level][0]
                    assert len({slots[x] for x in occurrences}) == len(occurrences)
                    checked_cells += 1
    print(f"{shapes} trees, {checked_cells} strict cells: "
          "transport paths and injectivity on occupied slots verified")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("max_edges", type=int, nargs="?", default=7)
    args = parser.parse_args()
    if args.max_edges < 0:
        parser.error("max_tree_edges must be nonnegative")
    check(args.max_edges)
