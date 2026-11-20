"""Strict six-cube sweeps and a CaTT multi-cell boundary certificate in rank three."""
from argparse import ArgumentParser
from collections import Counter
from itertools import combinations
from pathlib import Path

from canonical_gray_cube import build_cube, mask, square_chain
from catt import arr, check_ctx, comp2, infer, src, tgt, v
from emit_agda import Emitter
from rc2 import kappa, lfold, path
from relative_coherence_cube_boundary import boundary


def differential(chain):
    result = Counter()
    for face, coefficient in chain.items():
        for child, sign in boundary(face):
            result[child] += sign * coefficient
    return Counter({face: c for face, c in result.items() if c})


def closure(faces):
    cells = set(faces)
    pending = list(cells)
    while pending:
        for child, _ in boundary(pending.pop()):
            if child not in cells:
                cells.add(child)
                pending.append(child)
    return cells


def block_distance(row, incident):
    """Shortest adjacent-swap distance between the two contiguous-star conditions."""
    changes = {ridge: differential({ridge: 1}) for ridge in row}
    ports = {}
    for ridge, delta in changes.items():
        for port, sign in delta.items():
            ports.setdefault(port, []).append((ridge, sign))
    assert all(len(entries) == 1 or (len(entries) == 2 and entries[0][1] == -entries[1][1])
               for entries in ports.values())
    blocks = [row.intersection(differential({facet: 1})) for facet in incident]
    assert [len(block) for block in blocks] == [5, 5]
    assert len(blocks[0] & blocks[1]) == 1

    def orders(remaining, state, prefix):
        if not remaining:
            yield prefix
        for ridge in remaining:
            if -changes[ridge] <= state:
                after = state.copy()
                after.update(changes[ridge])
                yield from orders(remaining - {ridge}, +after, (*prefix, ridge))

    words = set(orders(row, -differential(dict.fromkeys(row, 1)), ()))

    def contiguous(word, block):
        positions = [i for i, ridge in enumerate(word) if ridge in block]
        return positions[-1] - positions[0] + 1 == len(block)

    start, finish = [{word for word in words if contiguous(word, block)} for block in blocks]
    assert start and finish
    seen = set(start)
    front = start
    distance = 0
    while front.isdisjoint(finish):
        neighbors = {word[:i] + (word[i + 1], word[i]) + word[i + 2:]
                     for word in front for i in range(len(word) - 1)}
        front = (neighbors & words) - seen
        assert front
        seen.update(front)
        distance += 1
    def inversions(first, second):
        rank = {ridge: i for i, ridge in enumerate(second)}
        return sum(rank[a] > rank[b] for a, b in combinations(first, 2))

    assert distance == min(inversions(a, b) for a in start for b in finish)
    return len(words), distance


def sweeps(dimension):
    top = (0,) * dimension
    signed = differential({top: 1})
    lower = differential(-signed)
    assert lower == differential(+signed)
    poles = set()
    previous = lower
    while any(face.count(0) for face in previous):
        next_row = differential(-previous)
        assert next_row == differential(+previous)
        poles.update(next_row)
        previous = next_row
    assert sum((+previous).values()) == sum((-previous).values()) == 1

    walks, labels, incidences = [], set(), {}
    for hemisphere in (-signed, +signed):
        unused = set(hemisphere)
        row = -lower
        route = []
        while True:
            support = closure(row)
            assert poles <= support and differential(row) == differential(-lower)
            assert all(c == 1 for c in row.values())
            labels.add(frozenset(row))
            if dimension == 6:
                assert [sum(f.count(0) == k for f in support) for k in range(5)] == [
                    57, 156, 165, 80, 15]
            if not unused:
                break
            # A single-facet tableau needs its negative subchain in this row.
            face, = [face for face in unused if -differential({face: 1}) <= row]
            incidences.setdefault(frozenset(row), []).append(face)
            after = row.copy()
            after.update(differential({face: 1}))
            assert all(c >= 0 for c in after.values())
            change = after.copy()
            change.subtract(row)
            assert change == differential({face: 1})
            route.append(face)
            row = +after
            incidences.setdefault(frozenset(row), []).append(face)
            unused.remove(face)
        assert row == +lower
        walks.append(route)
    assert len(labels) == 2 * dimension
    assert [next(i for i, x in enumerate(f) if x) for f in walks[0]] == list(range(dimension))
    assert [next(i for i, x in enumerate(f) if x) for f in walks[1]] == list(reversed(range(dimension)))
    if dimension == 6:
        counts = Counter(block_distance(row, pair) for row, pair in incidences.items())
        assert counts == {(12, 0): 4, (196, 6): 4, (286, 6): 2, (840, 8): 2}
        print("nested four-dimensional walks: 4 common block orders; "
              "6 rows need six swaps and 2 rows need eight swaps")
    return walks


def literal_three_cube(agda_path):
    # Use only the vertices, edges and squares of the known declaration.
    context = build_cube()[0][:-1]
    edges = iter(v(i) for i in range(8, 20))
    edge = {(base, axis): next(edges) for base in range(8) for axis in range(3)
            if not base & (1 << axis)}
    squares = iter(v(i) for i in range(20, 26))
    steps, facet_generator = {}, {}
    for base in range(8):
        for axes in combinations(range(3), 2):
            if base & mask(axes):
                continue
            fixed, = set(range(3)) - set(axes)
            upper = bool(base & (1 << fixed))
            face = tuple(0 if i in axes else 1 if upper else -1 for i in range(3))
            square = next(squares)
            facet_generator[face] = square
            steps[face] = (comp2(context, 0, edge[0, fixed], square) if upper else
                           comp2(context, 0, square, edge[mask(axes), fixed]))
    minus, plus = [[steps[f] for f in walk] for walk in sweeps(3)]

    def declare(source, target):
        nonlocal context
        ty = infer(context, source)
        assert ty == infer(context, target)
        generator = v(len(context))
        context += (arr(ty, source, target),)
        return generator

    replacements = {}
    corrections = Counter()

    def bridge(left, right, sign):
        assert path(context, left)[0] == path(context, right)[0]
        bridge_cell = declare(left, right)
        corrections[bridge_cell] = sign
        replacements[bridge_cell] = kappa(context, left, right)
        return bridge_cell

    def string(steps, sign):
        cells = [steps[0]]
        for left, right in zip(steps, steps[1:]):
            cells.extend([bridge(tgt(context, left), src(context, right), sign), right])
        return cells

    negative_parts = string(minus, -1)
    negative = lfold(context, 1, negative_parts)
    positive_parts = [bridge(src(context, minus[0]), src(context, plus[0]), 1)]
    positive_parts += string(plus, 1)
    positive_parts.append(bridge(tgt(context, plus[-1]), tgt(context, minus[-1]), 1))
    positive = lfold(context, 1, positive_parts)

    def incidence(generator):
        target_chain = square_chain(tgt(context, generator))
        target_chain.subtract(square_chain(src(context, generator)))
        return target_chain

    comparison = declare(negative, positive)
    total = incidence(comparison)
    assert len(corrections) == 6
    fillers = []
    for hole, witness in replacements.items():
        filler = declare(witness, hole)
        fillers.append(filler)
        assert incidence(filler) == Counter({hole: 1})
        for term, count in incidence(filler).items():
            total[term] -= corrections[hole] * count
    expected = Counter({facet_generator[face]: sign for face, sign in boundary((0, 0, 0))})
    assert total == expected and len(expected) == 6
    check_ctx(context)
    if agda_path:
        emitter = Emitter()
        for i, generator in enumerate([comparison, *fillers]):
            emitter.check_typed(f"column-{i}", context, generator)
        agda_path.write_text(emitter.module(agda_path.stem, "Seven-column cube-boundary certificate."))
    print("three-cube: seven typed 3-columns sum with signs to the six oriented squares")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path)
    args = parser.parse_args()
    sweeps(6)
    print("six-cube: two forced six-step sweeps; twelve distinct 4-rows, each with 57 vertices and 15 ridges")
    literal_three_cube(args.agda)
