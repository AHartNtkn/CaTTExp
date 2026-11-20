"""Check total opposition on distant exchanges and the mixed column at a pure boundary."""
import argparse
from collections import Counter
from itertools import product
from pathlib import Path

from catt import comp2, infer, maximal_vars, src, tgt, tree_ctx, v
from emit_agda import Emitter
from gray_globe_attachments import ordered_factors
from gray_globe_corner_prisms import fold
from gray_globe_end_charts import flatten, peel, span
from gray_globe_exterior_actions import arity, certificate
from gray_globe_factorizations import rank, truncate
from gray_globe_marked_column import copy_label, cylinder
from gray_globe_middle_parameter import full_state
from gray_globe_middle_steps import chart_tree
from gray_globe_pure_extension import raise_argument
from gray_globe_run_transport import peak, positions, runs
from gray_globe_section import EMPTY_ROW, cells, row_map
from gray_globe_sector_terms import arrow
from gray_globe_strip_squares import chart_lift, lift_on
from gray_path_wedge import compose


def reflect(cell):
    def chain(labels):
        return tuple(sorted(tuple((i, 1 - t if t < 2 else t) for i, t in g) for g in labels))
    return tuple((chain(target), chain(source)) for source, target in cell)


def run_factors(cell, cut, groups):
    gap = groups[0][1] + 1
    bit, = (x for (i, x), _ in cell[cut][0] if i == gap - 1)
    assert bit in (0, 1)
    owners = {}
    for row in cell[cut + 1:]:
        for g in row[0]:
            i, j = rank(g)
            group, = (a for a, b in groups if a <= max(0, cut + 1 - j) <= min(cut + 1, i) <= b)
            owners[i, j] = -group if bit else group
    return ordered_factors(cell, cut, owners)


def check_opposition(bound):
    domain = cells((bound, bound)) - {()}
    counts = Counter()
    for cell in domain:
        other = reflect(cell)
        assert other in domain and reflect(other) == cell
        assert (cell == other) == (cell == peak(bound, bound))
        for j, row in enumerate(cell):
            indices = tuple(g[0][0] for g in row[0])
            if indices != positions(bound, bound, j):
                break
        else:
            continue
        cut = j - 1
        groups = runs(indices)
        if len(groups) > 1:
            pieces = run_factors(cell, cut, groups)
            assert run_factors(other, cut, groups) == tuple(map(reflect, reversed(pieces)))
            counts['multiple runs'] += 1
        else:
            a, b = groups[0]
            if any(i < a - 1 or i > b for i in positions(bound, bound, cut)):
                assert truncate(cell, cut, 0) != truncate(other, cut, 0)
                counts['padded single run'] += 1
    print(f'Opposition on {len(domain)} cells of the {bound}-by-{bound} rectangle: {dict(counts)}.')


def patch(m, n, k, sign):
    left, right = k - n, m
    bits = (sign,) * (m + n - k - 1) + (1 - sign,)
    state = full_state(m, n, k, bits)
    result = []
    for first, last in ((left, right), (right, left)):
        word = flatten(state, k, first, last)
        path = word[:2] if sign == 0 else word[1:]
        assert {span(t, k) for t in path} == {(left, left), (right, right)}
        assert truncate(path[0], k - 1, 1) == truncate(path[1], k - 1, 0)
        result.append(path)
    return result


def check_column(m, k, paths):
    d = k - 1
    horizontal, vertical = [None, None], [None, None]
    for path in paths:
        i = j = 0
        for step in path:
            if span(step, k) == (m, m):
                vertical[i] = step
                j += 1
            else:
                horizontal[j] = step
                i += 1
        assert i == j == 1

    def collapse(g):
        (i, x), q = g
        return ((i, 2 if i == m - 1 else x), q) if i < m else None

    old = row_map(horizontal[0], 0, collapse)
    assert len(old) == k + 1 and row_map(horizontal[1], 0, collapse) == old
    for i, edge in enumerate(vertical):
        state = truncate(old, d, i)
        assert cylinder(state, m - 1) == edge and row_map(edge, 0, collapse) == state
        marked = tuple(g for g in state[-1][0] if g[0][0] == m - 1)
        assert marked == (((m - 1, 2), edge[-1][0][0][1]),)
    for j, edge in enumerate(horizontal):
        parts, active_index = peel(edge, d, m)
        active, fixed = parts[active_index], parts[1 - active_index]
        assert active_index == j and active == row_map(old, 0, lambda g: copy_label(g, m - 1, j))
        assert fixed == cylinder(truncate(old, d - 1, 1 - j), m - 1)
        padded = fixed + (EMPTY_ROW,)
        assert (compose(padded, active, d - 1) if j else compose(active, padded, d - 1)) == edge
    whole = cylinder(old, m - 1)
    assert whole[-1] == EMPTY_ROW
    assert all(compose(first, last, d) == whole[:-1] for first, last in paths)


def check_patches(bound):
    counts = Counter()
    for m, n in product(range(3, bound + 1), repeat=2):
        for k in range(max(m, n) + 1, m + n - 1):
            prefix, suffix = (patch(m, n, k, sign) for sign in (0, 1))
            assert [tuple(map(reflect, reversed(p))) for p in prefix] == suffix
            counts['pairs of patches'] += 1
            if m == k - 1:
                for paths in (prefix, suffix):
                    check_column(m, k, paths)
                    counts['right columns'] += 1
    print(f'Bounds through {bound}: {dict(counts)}.')


def check_open_square(d, emitter):
    """An independent native change crosses a generator with two composite faces."""
    k, cut = d + 1, d - 2
    ctx = arity(cut, (k, d))
    native, old = map(v, maximal_vars(ctx))
    x0, y0 = src(ctx, old), tgt(ctx, old)

    def fresh(ty):
        nonlocal ctx
        term = v(len(ctx))
        ctx += (ty,)
        return term

    x1, y1 = (fresh(infer(ctx, term)) for term in (x0, y0))
    ex = fresh(arrow(ctx, x0, x1))
    ey = fresh(arrow(ctx, y0, y1))
    new = fresh(arrow(ctx, x1, y1))

    def sequence(*terms):
        return fold(ctx, d - 1, terms)

    def word(*terms):
        return fold(ctx, d, terms)

    def spatial(left, right):
        return comp2(ctx, cut, left, right)

    mixed = fresh(arrow(ctx, sequence(old, ey), sequence(ex, new)))

    def open_column(w):
        u, v_end = src(ctx, w), tgt(ctx, w)
        cap_y = raise_argument(ctx, spatial(v_end, y0), y0, ey)
        cap_x = raise_argument(ctx, spatial(u, x0), x0, ex)
        before = sequence(spatial(w, old), cap_y)
        after = sequence(cap_x, spatial(w, new))
        core = spatial(w, mixed)
        layout = tree_ctx(chart_tree((cut, d, (d - 1, d, d))))
        initial = lift_on(ctx, layout, (w, old, ey), before, src(ctx, core))
        terminal = lift_on(ctx, layout, (w, ex, new), tgt(ctx, core), after)
        return initial, core, terminal

    w0, w1 = src(ctx, native), tgt(ctx, native)
    initial, terminal = map(open_column, (w0, w1))
    states = (src(ctx, initial[0]), *(tgt(ctx, t) for t in initial))
    actions = tuple(raise_argument(ctx, t, w0, native) for t in states)
    layout = tree_ctx(chart_tree((cut, k, (d - 1, d, d))))
    charts = ((layout, (native, old, ey)), (arity(cut, (k, k)), (native, mixed)),
              (layout, (native, ex, new)))
    squares = [lift_on(ctx, tree, labels, word(initial[i], actions[i + 1]), word(actions[i], terminal[i]))
               for i, (tree, labels) in enumerate(charts)]

    current = word(*initial, actions[-1])
    steps = []
    for i in reversed(range(len(squares))):
        left, right = initial[:i], terminal[i + 1:]
        step = word(*left, squares[i], *right)
        if src(ctx, step) != current:
            letters = (*left, initial[i], actions[i + 1], *right)
            steps.append(chart_lift(ctx, letters, d, current, src(ctx, step)))
        steps.append(step)
        current = tgt(ctx, step)
    goal = word(actions[0], word(*terminal))
    if current != goal:
        steps.append(chart_lift(ctx, (actions[0], *terminal), d, current, goal))
    square = fold(ctx, k, steps)
    wanted = arrow(ctx, word(word(*initial), actions[-1]), goal)
    assert infer(ctx, square) == wanted
    if emitter:
        certificate(emitter, ctx)('column-square', square, wanted)
    print(f'Checked the column square with composite generator boundaries in degree {k + 1}.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bound', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.bound < 3:
        parser.error('mixed exchanges start at globe bound three')
    check_opposition(min(5, args.bound))
    check_patches(args.bound)
    out = Emitter() if args.agda else None
    check_open_square(3, out)
    if out:
        args.agda.write_text(out.module(args.agda.stem, 'An unmarked native change across a mixed column.'))
