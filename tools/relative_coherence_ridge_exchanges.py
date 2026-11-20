"""Joint lower diagrams for the six-cube ridge exchanges in Researcher Response 19."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import combinations
from pathlib import Path

from catt import arr, comp2, comp_tree, infer, maximal_vars, src, tdim_tm, tgt, tree_ctx, v
from emit_agda import Emitter
from gray_globe_comparison import strict_cells
from relative_coherence_cube_boundary import boundary
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_facet_sweeps import closure, differential


@cache
def delta(face):
    return differential({face: 1})


def step(row, change):
    assert -change <= row
    after = row.copy()
    after.update(change)
    assert all(n in (0, 1) for n in after.values())
    return +after


def membranes():
    two_sides = delta((0,) * 6)
    initial = -differential(-two_sides)
    result = set()
    for side in (-two_sides, +two_sides):
        row = initial
        remaining = set(side)
        while remaining:
            result.add(frozenset(row))
            facet, = [f for f in remaining if -delta(f) <= row]
            row = step(row, delta(facet))
            remaining.remove(facet)
        result.add(frozenset(row))
    return result


def forks(membrane):
    visited = set()

    def visit(done, state):
        if done in visited:
            return
        visited.add(done)
        enabled = sorted(ridge for ridge in membrane - done if -delta(ridge) <= state)
        yield frozenset(state), enabled
        for ridge in enabled:
            yield from visit(done | {ridge}, step(state, delta(ridge)))

    yield from visit(frozenset(), -differential(dict.fromkeys(membrane, 1)))


def profile(cells, height):
    return tuple(sum(face.count(0) == k for face in cells) for k in range(height + 1))


def joint_sequence(state, a, b):
    # Compress the two disjoint four-cube inputs to two marked 3-cells.
    before = Counter(state)
    consumed = (-delta(a)) + (-delta(b))
    assert len(consumed) == 8 and consumed <= before
    changes = {f: delta(f) for f in before - consumed}
    for ridge in (a, b):
        changes[ridge] = differential(-delta(ridge))
        assert changes[ridge] == differential(+delta(ridge))
    layer = -differential(before)
    finish = +differential(before)
    assert len(changes) == 14
    remaining = set(changes)
    order = []
    while remaining:
        available = [f for f in remaining if -changes[f] <= layer]
        assert available
        gate = min(available)
        order.append(gate)
        layer = step(layer, changes[gate])
        remaining.remove(gate)
    assert layer == finish
    # Verify all four strict expansions of this *one* diagram in the original basis.
    for changed in (set(), {a}, {b}, {a, b}):
        expansion = Counter()
        for gate in order:
            if gate in (a, b):
                expansion.update(+delta(gate) if gate in changed else -delta(gate))
            else:
                expansion[gate] += 1
        expected = before.copy()
        for ridge in changed:
            expected.update(delta(ridge))
        assert expansion == expected
    i, j = sorted((order.index(a), order.index(b)))
    return i > 0, i + 1 < j, j + 1 < len(order)


def exchange_term(pattern):
    pre, middle, post = pattern
    dimensions = [3] * pre + [4] + [3] * middle + [4] + [3] * post
    ctx = tree_ctx(string_tree(2, dimensions))
    slots = list(map(v, maximal_vars(ctx)))
    indices = [i for i, d in enumerate(dimensions) if d == 4]

    def route(order):
        values = [src(ctx, t) if d == 4 else t for t, d in zip(slots, dimensions)]
        sides = []
        for i in order:
            values[i] = slots[i]
            arity = string_tree(2, [tdim_tm(ctx, t) for t in values])
            sides.append(comp_tree(arity, ctx, values))
            values[i] = tgt(ctx, slots[i])
        return comp2(ctx, 3, *sides)

    forward, reverse = route(indices), route(indices[::-1])
    assert forward != reverse
    term = head(ctx, forward, reverse)
    assert infer(ctx, term) == arr(infer(ctx, forward), forward, reverse)
    return ctx, term


def check_projection():
    facets = dict(boundary((0,) * 4))
    minus, plus = [closure(f for f in tuple(facets) if facets[f] == sign) for sign in (-1, 1)]
    assert [len({v for v in closure([(0,) * 4]) - half if 0 not in v})
            for half in (minus, plus)] == [1, 1]
    counts = Counter()
    for cell in strict_cells((1,) * 4, 3):
        faces = {tuple(0 if rank else 2 * tag - 1 for rank, tag in face)
                 for row in cell for side in row for face in side}
        support = closure(faces)
        counts[support <= minus, support <= plus] += 1
    assert counts == {(True, True): 230, (False, True): 145, (True, False): 145}
    print("four-cube: every one of the 520 strict 3-cells lies in a signed hemisphere")


def check(agda_path):
    states, edges, squares = set(), set(), set()
    membranes_to_test = membranes()
    assert len(membranes_to_test) == 12
    common_lower_rows = set()
    for membrane in membranes_to_test:
        bottom = -differential(dict.fromkeys(membrane, 1))
        lower_rows = []
        while any(face.count(0) for face in bottom):
            lower = differential(bottom)
            lower_rows.append(tuple(sorted(lower.items())))
            bottom = -lower
        common_lower_rows.add(tuple(lower_rows))
        for state, enabled in forks(membrane):
            assert differential(Counter(state)) == dict(lower_rows[0])
            states.add(state)
            edges.update((state, a) for a in enabled)
            squares.update((state, a, b) for a, b in combinations(enabled, 2))
    assert (len(states), len(edges), len(squares)) == (148, 264, 114)
    (lower_rows,) = common_lower_rows
    lower_faces = {f for row in lower_rows for f, count in row}
    for state in states:
        assert lower_faces <= closure(state)
        assert profile(closure(state), 3) == (42, 96, 75, 20)
    for state, ridge in edges:
        before = closure(state)
        after = closure(step(Counter(state), delta(ridge)))
        unary = closure(state | {ridge})
        assert profile(unary, 4) == (43, 100, 81, 24, 1)
        assert unary - {ridge} == before | after
        axes = [i for i, coord in enumerate(ridge) if not coord]
        differences = [{tuple(v[i] for i in axes) for v in (left - right) if 0 not in v}
                       for left, right in [(before, after), (after, before)]]
        assert set.union(*differences) == {(-1, 1, -1, 1), (1, -1, 1, -1)}
    patterns = Counter(joint_sequence(*square) for square in squares)
    assert sorted(patterns.values()) == [2, 18, 19, 19, 56]
    emitter = Emitter()
    for pattern in sorted(patterns):
        ctx, term = exchange_term(pattern)
        emitter.check_type("exchange-" + "".join(str(int(p)) for p in pattern),
                           ctx, term, infer(ctx, term))
    if agda_path:
        agda_path.write_text(emitter.module(agda_path.stem, "Joint six-cube ridge exchanges."))
    print("148 states, 264 one-ridge steps, 114 joint 14-row diagrams and five typed 5-cell arities")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path)
    args = parser.parse_args()
    check_projection()
    check(args.agda)
