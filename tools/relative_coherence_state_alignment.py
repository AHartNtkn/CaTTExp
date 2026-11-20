"""Select lower states by matching the operations and arguments of two elementary paths."""
from functools import cache
from itertools import product

from catt import arr, infer, src, subst_tm, tdim, tdim_tm, tgt
from relative_coherence_chart_joins import readings
from relative_coherence_intermediates import charts, terms_of_rank
from relative_coherence_state_paths import at, occurrence, serialize


def select_states(ctx, start, first, second):
    """Return a sufficient Response 9 vocabulary for a matched decomposition, or None."""
    rank = tdim_tm(ctx, start)
    def vertices(base, path):
        states = [base]
        for edge in path:
            assert src(ctx, edge) == states[-1]
            states.append(tgt(ctx, edge))
        return tuple(states)

    @cache
    def options(state):
        groups = {}
        for chart in charts(ctx, state):
            low = tuple(None if tdim(ty)+1 == rank else term
                        for ty, term in zip(chart.arity, chart.labels, strict=True))
            key = chart.arity, infer(chart.arity, chart.term), low
            groups.setdefault(key, []).append(chart)
        return groups

    @cache
    def moves(edge, a, b):
        choices = []
        if a.labels == b.labels:
            expected = arr(infer(a.arity, a.term), a.term, b.term)
            if any(infer(a.arity, h) == expected for h in readings(a.arity, a.labels, edge)):
                choices.append(None)  # The operation changes at a fixed tuple.
        if a.term == b.term:
            for j, ty in enumerate(a.arity):
                if tdim(ty)+1 != rank:
                    continue
                if any(x != y for i, (x, y) in enumerate(zip(a.labels, b.labels, strict=True)) if i != j):
                    continue
                address = occurrence(a.term, j)
                state = subst_tm(a.term, a.labels)
                for inner in terms_of_rank(ctx, (edge,), rank+1):
                    if infer(ctx, inner)[2:] == (a.labels[j], b.labels[j]) and at(ctx, state, address, inner) == edge:
                        choices.append((j, inner))
        return tuple(choices)

    @cache
    def solve(base, p, q):
        left, right = vertices(base, p), vertices(base, q)
        assert left[-1] == right[-1]
        if p == q:
            return frozenset(left)
        if p and q and p[0] == q[0]:
            inner = solve(tgt(ctx, p[0]), p[1:], q[1:])
            if inner is not None:
                return inner | {base}
        if p and q and p[-1] == q[-1]:
            inner = solve(base, p[:-1], q[:-1])
            if inner is not None:
                return inner | {left[-1]}
        # Walk the two paths as a cycle of readings. The reverse half retains
        # the original direction of its edges for the typing checks.
        ring = left[:-1] + right[:0:-1]
        route = p + q[::-1]
        keys = [key for key in options(base) if all(key in options(s) for s in ring)]
        for key in keys:
            slots = [j for j, entry in enumerate(key[2]) if entry is None]
            def finish(chosen, steps):
                ref = chosen[0]
                values = {j: {a.labels[j] for a in chosen} for j in slots}
                result = set(ring)
                for j in slots:
                    def coordinate(actions):
                        return tuple(action[1] for action in actions if action is not None and action[0] == j)
                    pj, qj = coordinate(steps[:len(p)]), coordinate(steps[len(p):][::-1])
                    arg = ref.labels[j]
                    if (arg, pj, qj) == (base, p, q):
                        return None
                    child = solve(arg, pj, qj)
                    if child is None:
                        return None
                    child = terms_of_rank(ctx, child, rank)
                    result.update(child)
                    ty = infer(ctx, arg)
                    values[j].update(x for x in child if infer(ctx, x) == ty)
                for row in product(*(values[j] for j in slots)):
                    labels = list(ref.labels)
                    for j, value in zip(slots, row, strict=True):
                        labels[j] = value
                    result.add(subst_tm(ref.term, labels))
                return frozenset(result)

            def extend(chosen, steps):
                i = len(steps)
                close = i+1 == len(route)
                next_charts = [chosen[0]] if close else options(ring[i+1])[key]
                for next_chart in next_charts:
                    a, b = chosen[-1], next_chart
                    if i >= len(p):
                        a, b = b, a
                    for step in moves(route[i], a, b):
                        result = (finish(chosen, steps+(step,)) if close else
                                  extend(chosen+(next_chart,), steps+(step,)))
                        if result is not None:
                            return result
                return None

            for chart in options(base)[key]:
                found = extend((chart,), ())
                if found is not None:
                    return found
        return None

    return solve(start, tuple(first), tuple(second))


def check():
    from catt import comp2, disc_tree, maximal_vars, sub_from, tree_ctx, v
    from relative_coherence_chart_joins import composite_state, schedule, wedge_switches
    from relative_coherence_exchange_faces import head, string_tree
    from relative_coherence_state_paths import integer_span, path_matrix
    from relative_coherence_intermediates import example

    ctx, edges, _ = wedge_switches(4, 3)
    trunk = tree_ctx(string_tree(0, [3]*3))
    nodes, p = schedule(ctx, trunk, edges, (0, 1, 2))
    other, q = schedule(ctx, trunk, edges, (2, 1, 0))
    assert nodes[0] == other[0]
    states = select_states(ctx, nodes[0], p, q)
    assert states is not None
    cube = {composite_state(ctx, trunk, corner)
            for corner in product(*(infer(ctx, e)[2:] for e in edges))}
    assert cube <= states and cube - set(nodes) - set(other)
    print(f'Opposite schedules: all {len(cube)} corners selected from the two paths.', flush=True)

    # Use a single whiskered switch so the state matrix is small enough
    # to check the selected vocabulary independently of the decomposition.
    ctx, (edge,), _ = wedge_switches(4, 1)
    f, g = infer(ctx, edge)[2:]
    disk = tree_ctx(disc_tree(3))
    j, = maximal_vars(disk)
    op = head(disk, src(disk, v(j)), tgt(disk, v(j)))
    cap = head(disk, v(j), op)
    def apply(term, arg):
        return subst_tm(term, sub_from(disk, ctx, {j:arg}))
    u = comp2(ctx, 3, edge, apply(cap, g))
    w = comp2(ctx, 3, apply(cap, f), at(ctx, apply(op, f), (j,), edge))
    states = select_states(ctx, f, serialize(ctx, u), serialize(ctx, w))
    assert states is not None
    target, cols = path_matrix(ctx, u, w, states)
    assert any(target) and integer_span(target, cols)
    print(f'Mixed square: selected {len(states)} states and verified the integer certificate.', flush=True)

    ctx, inner_u, inner_w, *_ = example(4)
    f = src(ctx, inner_u)
    assert infer(ctx, inner_u)[2:] == infer(ctx, inner_w)[2:] == (f, f)
    outer_u = comp2(ctx, 3, inner_u, apply(cap, f))
    outer_w = comp2(ctx, 3, apply(cap, f), at(ctx, apply(op, f), (j,), inner_w))
    # The projected coordinate paths now differ. Their comparison itself
    # has to pass inside the fixed whisker in the weakly presented globe.
    states = select_states(ctx, f, serialize(ctx, outer_u), serialize(ctx, outer_w))
    assert states is not None
    target, cols = path_matrix(ctx, outer_u, outer_w, states)
    assert any(target) and integer_span(target, cols)
    print(f'Nested mixed square: verified the integer certificate on {len(states)} selected states.', flush=True)


if __name__ == '__main__':
    check()
