"""Audit the signed links for simultaneous spatially independent marker boxes."""
from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, permutations, product

from relative_coherence_local_links import Circuits, FACES
from semistrict_surface_two_marker_cuts import sides


def spatial(diagrams, markers):
    # The inherited marker sets record paths through any number of ordinary gates.
    return all(not diagrams.markers[wire] for _, inputs in markers for wire in inputs)


def flag_check(corners):
    totals = Counter()
    for faces in corners.values():
        if any(n != 1 for n in faces.values()):
            raise AssertionError('non-unique cube at prescribed signed germs')
        germs = {next(iter(f)) for f in faces if len(f) == 1}
        for face in faces:
            totals[len(face)] += 1
            if len(face) < 2:
                continue
            for candidate in germs - face:
                if all(frozenset((candidate, other)) in faces for other in face):
                    assert face | {candidate} in faces
    return sorted(totals.items())


def circuit_links(inputs, bound):
    diagrams = Circuits(inputs, {k: FACES[k] for k in 'UABVW'})
    corners = defaultdict(Counter)
    omitted = Counter()
    exchange_frames = defaultdict(list)
    for frontier, markers in diagrams.enumerate(bound):
        independent = spatial(diagrams, markers)
        if len(markers) == 2:
            ends = (sides(diagrams, frontier, *markers), sides(diagrams, frontier, *reversed(markers)))
            exchange_frames[tuple(sorted(ends))].append(independent)
        if not independent:
            omitted[len(markers)] += 1
            continue
        for signs in product((0, 1), repeat=len(markers)):
            choices = dict(zip(markers, signs))
            source = diagrams.expand(frontier, choices)
            germs = frozenset((choices[m], diagrams.expand(frontier, choices, (m,))) for m in markers)
            assert len(germs) == len(markers)
            corners[source][germs] += 1
    double_edges = [flags for flags in exchange_frames.values() if len(flags) > 1]
    assert double_edges and all(flags == [False, False] for flags in double_edges)
    return flag_check(corners), sum(omitted.values()), len(double_edges)


def stationary_links(width):
    # Each box is a genuine directed loop at the same identity diagram, including
    # boxes on a composite path. Its two signed germs are distinct.
    corners = Counter()
    intervals = [(i, i+n) for n in (1, 2) for i in range(width+1-n)]
    for size in range(width + 1):
        for row in combinations(intervals, size):
            if any(a < d and c < b for (a,b),(c,d) in combinations(row, 2)):
                continue
            for signs in product((0, 1), repeat=size):
                corners[frozenset(zip(row, signs))] += 1
    return flag_check({0: corners})


def stacking_and_juxtaposition():
    diagrams = Circuits(6, {k: FACES[k] for k in 'UVW'})
    start = diagrams.inputs
    frame = diagrams.apply('V', 0, start)
    frame = diagrams.apply('W', 1, frame)
    markers = lambda end: frozenset().union(*(diagrams.markers[w] for w in end))
    # The second marker meets a live output of the first.
    assert not spatial(diagrams, markers(frame))
    outer = diagrams.apply('V', 0, start)
    outer = diagrams.apply('W', 2, outer)
    marked = markers(outer)
    assert len(marked) == 2 and spatial(diagrams, marked)
    # A later gate can connect the two pieces without ordering their markers.
    joined = diagrams.apply('r', 1, outer)
    assert markers(joined) == marked and spatial(diagrams, marked)


@cache
def sorting_paths(order):
    if order == tuple(sorted(order)):
        return {()}
    paths = set()
    for i in range(len(order) - 1):
        if order[i] > order[i + 1]:
            smaller = order[:i] + (order[i + 1], order[i]) + order[i + 2:]
            paths.update((i,) + rest for rest in sorting_paths(smaller))
    return paths


def frame_routes(slots):
    total = squares = hexagons = 0
    for order in permutations(range(slots)):
        paths = sorting_paths(order)
        reached = {next(iter(paths))}
        queue = list(reached)
        while queue:
            path = queue.pop()
            neighbors = []
            for i, (a, b) in enumerate(zip(path, path[1:])):
                if abs(a-b) > 1:
                    neighbors.append(path[:i] + (b, a) + path[i+2:])
                    squares += 1
                if abs(a-b) == 1 and path[i+2:i+3] == (a,):
                    neighbors.append(path[:i] + (b, a, b) + path[i+3:])
                    hexagons += 1
            for other in neighbors:
                assert other in paths
                if other not in reached:
                    reached.add(other)
                    queue.append(other)
        assert reached == paths
        total += len(paths)
    return total, squares // 2, hexagons // 2


if __name__ == '__main__':
    stacking_and_juxtaposition()
    for n, bound in [(5, 3), (4, 4)]:
        counts, omitted, circles = circuit_links(n, bound)
        print(f'{n} inputs, {bound} gates: signed corners {counts}, {omitted} dependent frames, {circles} two-sheet circles preserved')
    print('stationary-marker signed links on six wires:', stationary_links(6))
    for slots in (3, 4, 5):
        print(f'{slots} slots: sorting routes, square moves, hexagon moves:', frame_routes(slots))
