"""Compute track equality and the first higher homotopy degree for a unary seam label."""

from argparse import ArgumentParser
from collections import Counter, defaultdict, deque
from itertools import combinations, permutations

from relative_coherence_coloured_faces import visible
from relative_coherence_seam_cycles import two_bridges
from relative_coherence_strip_fibres import Complex


class SeamGraph:
    def __init__(self, size, arcs):
        self.size = size
        self.arcs = set(arcs)
        if size < 1 or any(i == j or min(i, j) < 0 or max(i, j) >= size for i, j in self.arcs):
            raise ValueError('provide a nonempty loop-free seam graph with vertices 0 through size-1')
        self.blocked = {(i, j) for i, j in self.arcs if (j, i) in self.arcs}

    def reduce(self, word):
        result = []
        for i in word:
            if not 0 <= i < self.size:
                raise ValueError('seam flip outside the graph')
            for j in range(len(result) - 1, -1, -1):
                if result[j] == i:
                    result.pop(j)
                    break
                if (result[j], i) in self.blocked:
                    result.append(i)
                    break
            else:
                result.append(i)
        return tuple(result)

    def first_hole(self):
        # A missing simplex in the flag completion contains no blocked pair.
        # A shortest directed cycle on such a subset is automatically induced.
        for count in range(3, self.size + 1):
            for vertices in combinations(range(self.size), count):
                if any(pair in self.blocked for pair in combinations(vertices, 2)):
                    continue
                remaining = set(vertices)
                while remaining:
                    sources = {v for v in remaining if all((u, v) not in self.arcs for u in remaining)}
                    if not sources:
                        return vertices
                    remaining -= sources
        return ()


def test_graphs():
    arcs = tuple(permutations(range(4), 2))
    totals = Counter()
    for bits in range(1 << len(arcs)):
        graph = SeamGraph(4, (a for i, a in enumerate(arcs) if bits & (1 << i)))
        hole = graph.first_hole()
        # Independent oracle: enumerate directed polygons and test every chord.
        induced = set()
        for length in (3, 4):
            for cycle in permutations(range(4), length):
                step = set(zip(cycle, cycle[1:] + cycle[:1]))
                on_cycle = {(i, j) for i, j in graph.arcs if i in cycle and j in cycle}
                if step == on_cycle:
                    induced.add(tuple(sorted(cycle)))
        assert hole == min(induced, key=lambda h: (len(h), h), default=())
        totals[len(hole)] += 1
    print('4096 seam graphs by smallest induced cycle of length at least three:', dict(sorted(totals.items())))


def test_typed_histories():
    obj = Complex(*two_bridges())
    graph = SeamGraph(3, [(0, 1), (1, 0), (1, 2), (2, 1)])
    assert not graph.first_hole()
    signs = [tuple(x > 0 for x in visible(cell, 3)) for cell in obj.cells]
    adjacency = defaultdict(list)
    arcs = {}
    for e, (degree, ends) in enumerate(zip(obj.degrees, obj.facets)):
        if degree != 1:
            continue
        a, b = ends
        def half(vertex):
            return tuple(i for i in range(3) if signs[vertex][i] != signs[e][i])
        word = half(a) + half(b)[::-1]
        arcs[e] = {a: (b, word), b: (a, word[::-1])}
        adjacency[a].append((b, word))
        adjacency[b].append((a, word[::-1]))

    faces = 0
    for degree, edges in zip(obj.degrees, obj.facets):
        if degree != 2:
            continue
        start = next(iter(arcs[edges[0]]))
        at, remaining, word = start, set(edges), ()
        while remaining:
            edge = next(e for e in remaining if at in arcs[e])
            remaining.remove(edge)
            at, segment = arcs[edge][at]
            word += segment
        assert at == start and not graph.reduce(word)
        faces += 1

    root = next(iter(adjacency))
    paths = {root: ()}
    queue = deque([root])
    loops = set()
    while queue:
        at = queue.popleft()
        for other, segment in adjacency[at]:
            new = graph.reduce(paths[at] + segment)
            if other not in paths:
                paths[other] = new
                queue.append(other)
            else:
                difference = graph.reduce(new + paths[other][::-1])
                if difference:
                    loops.add(difference)
    assert len(paths) == len(adjacency)
    assert any(graph.reduce(a + b + a[::-1] + b[::-1]) for a, b in combinations(loops, 2))
    print(f'{len(paths)} typed serial vertices, {len(arcs)} charts, {faces} two-cell boundaries, nontrivial track commutator')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--seams', type=int, help='number of seam coordinates')
    parser.add_argument('--arcs', nargs='*', default=[], metavar='I,J', help='directed arcs; indices start at zero')
    parser.add_argument('--word', nargs='*', type=int, default=[], help='flip indices, in execution order')
    args = parser.parse_args()
    if args.seams is None:
        if args.arcs or args.word:
            parser.error('specify --seams with graph or word input')
        test_graphs()
        test_typed_histories()
    else:
        try:
            g = SeamGraph(args.seams, [tuple(map(int, arc.split(','))) for arc in args.arcs])
            reduced = g.reduce(args.word)
            hole = g.first_hole()
        except ValueError as error:
            parser.error(str(error))
        print('path represents the identity:', not reduced)
        print('first nonzero higher homotopy degree:', len(hole) - 1 if hole else 'none')
        if hole:
            print('witness seam set:', *hole)
