"""Check the phase subdivision of three independent changes on suspended lax squares."""
from argparse import ArgumentParser
from functools import cache
from itertools import product
from pathlib import Path

from catt import (check_ctx, comp2, disc_tree, glue_tree, infer, maximal_vars, src,
                  sub_from, subst_tm, subst_ty, tdim_tm, tgt, tree_ctx, v)
from ct_suspension import ident, susp_ctx
from emit_agda import Emitter
from gray_globe_branch_comparisons import square_comparison
from gray_globe_exterior_actions import arity, certificate, coherence
from gray_globe_strip_squares import lift_on
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import composite


def next_state(state, axis):
    return tuple(p + int(i == axis) for i, p in enumerate(state))


@cache
def associator(cut, to_left):
    ar = arity(cut, (cut + 1,) * 3)
    a, b, c = map(v, maximal_vars(ar))
    left = composite(ar, cut, (a, b, c))
    right = comp2(ar, cut, a, comp2(ar, cut, b, c))
    return ar, coherence(ar, right, left) if to_left else coherence(ar, left, right)


def rebracket(ctx, cut, steps, *, to_left):
    # Form the associator before evaluation, allowing repeated actual inputs.
    ar, term = associator(cut, to_left)
    labels = sub_from(ar, ctx, dict(zip(maximal_vars(ar), steps, strict=True)))
    return subst_tm(term, labels)


def block_refinement(ctx, m, events):
    """Exchange one two-entry block with one entry, then specialize across three branches."""
    n = m + 1
    pair = tree_ctx(disc_tree(n) + disc_tree(n))
    x, y = map(v, maximal_vars(pair))

    def cross(g, a, b):
        return comp2(g, 0, a, b)

    def compare(g, p, q):
        assert infer(g, p) == infer(g, q)
        result = coherence(g, p, q)
        infer(g, result)
        return result

    def label(arity_ctx, target, slots):
        return sub_from(arity_ctx, target, dict(zip(maximal_vars(arity_ctx), slots, strict=True)))

    def order(g, x, y, left_first):
        if left_first:
            return comp2(g, m, cross(g, x, src(g, y)), cross(g, tgt(g, x), y))
        return comp2(g, m, cross(g, src(g, x), y), cross(g, x, tgt(g, y)))

    exchange = compare(pair, order(pair, x, y, True), order(pair, x, y, False))
    chain = glue_tree(n, m, n)
    grid = tree_ctx(chain + disc_tree(n))
    a, b, c = map(v, maximal_vars(grid))
    ab = comp2(grid, m, a, b)
    whole = subst_tm(exchange, label(pair, grid, (ab, c)))

    # Each distributor lives on the stationary face of the third globe.
    edge_ctx = tree_ctx(chain + disc_tree(m))
    i, j, fixed = map(v, maximal_vars(edge_ctx))
    expanded = comp2(edge_ctx, m, cross(edge_ctx, i, fixed), cross(edge_ctx, j, fixed))
    folded = cross(edge_ctx, comp2(edge_ctx, m, i, j), fixed)
    pre = subst_tm(compare(edge_ctx, expanded, folded), label(edge_ctx, grid, (a, b, src(grid, c))))
    post = subst_tm(compare(edge_ctx, folded, expanded), label(edge_ctx, grid, (a, b, tgt(grid, c))))
    ca = cross(grid, src(grid, a), c)
    cb = cross(grid, tgt(grid, b), c)
    coarse = composite(grid, n, (comp2(grid, m, pre, cb), whole, comp2(grid, m, ca, post)))

    a0, b0 = (cross(grid, t, src(grid, c)) for t in (a, b))
    a1, b1 = (cross(grid, t, tgt(grid, c)) for t in (a, b))
    ac = subst_tm(exchange, label(pair, grid, (a, c)))
    bc = subst_tm(exchange, label(pair, grid, (b, c)))
    middle = cross(grid, tgt(grid, a), c)
    # The initial product is left-associated, the final one right-associated.
    # Rebracket just where an adjacent pair is about to exchange.
    fine = composite(grid, n, (
        rebracket(grid, m, (a0, b0, cb), to_left=False),
        comp2(grid, m, a0, bc),
        rebracket(grid, m, (a0, middle, b1), to_left=True),
        comp2(grid, m, ac, b1),
        rebracket(grid, m, (ca, a1, b1), to_left=False)))
    comparison = compare(grid, coarse, fine)

    z, w, u = events
    # Two different physical addresses occupy the same reference block.
    actual = (cross(ctx, z, src(ctx, w)), cross(ctx, tgt(ctx, z), w), u)
    sigma = label(grid, ctx, actual)
    result = subst_tm(comparison, sigma)
    assert infer(ctx, result)[2:] == tuple(subst_tm(t, sigma) for t in (coarse, fine))
    return result


def check(d, emitter):
    m, n = d + 1, d + 2
    branch, _ = square_comparison()
    for _ in range(d):
        branch = susp_ctx(branch)
    ctx = branch
    top = v(len(branch) - 1)
    events = [top]
    end = 1
    for _ in range(2):
        ren = (v(end),) + tuple(v(len(ctx) + j) for j in range(len(branch) - 1))
        end = ren[1][1]
        ctx += tuple(subst_ty(ty, ren) for ty in branch[1:])
        events.append(subst_tm(top, ren))
    check_ctx(ctx)
    pairs = []
    for z in events:
        values = []
        for side in (src(ctx, z), tgt(ctx, z)):
            # The two spatial factors in the actual generator declaration.
            args = [side[3][j] for j in maximal_vars(side[1])]
            assert len(args) == 2 and comp2(ctx, d, *args) == side
            values.append(args)
        pairs.append(values)

    @cache
    def vertex(state):
        heads = []
        for j, phase in enumerate(state):
            a, b = pairs[j][int(phase >= 2)]
            if phase in (0, 3):
                # This writing uses a proper factor inside the source or target.
                b = comp2(ctx, d, b, ident(ctx, tgt(ctx, b)))
            heads.append(comp2(ctx, d, a, b))
        term = composite(ctx, 0, heads)
        if sum(state) % 2:
            term = comp2(ctx, d, term, ident(ctx, tgt(ctx, term)))
        return term

    def fill(state, moving, a, b):
        tree = ()
        labels = []
        for j, phase in enumerate(state):
            if phase == 1 and j in moving:
                tree += disc_tree(n)
                labels.append(events[j])
            elif j not in moving and phase in (1, 2):
                tree += disc_tree(m)
                labels.append((src if phase == 1 else tgt)(ctx, events[j]))
            else:
                tree += glue_tree(m, d, m)
                labels.extend(pairs[j][int(phase >= 2)])
        return lift_on(ctx, tree_ctx(tree), labels, a, b)

    @cache
    def edge(state, axis):
        return fill(state, (axis,), vertex(state), vertex(next_state(state, axis)))

    def edges(state, order):
        result = []
        for i in order:
            result.append(edge(state, i))
            state = next_state(state, i)
        return result

    @cache
    def square(state, i, j):
        a = composite(ctx, m, edges(state, (i, j)))
        b = composite(ctx, m, edges(state, (j, i)))
        return fill(state, (i, j), a, b)

    def swap(state, order, pos):
        i, j = order[pos:pos + 2]
        new = order[:pos] + (j, i) + order[pos + 2:]
        before, after = edges(state, order), edges(state, new)
        if pos == 0:
            result = comp2(ctx, m, square(state, i, j), before[2])
        else:
            face = square(next_state(state, order[0]), i, j)
            result = composite(ctx, n, (rebracket(ctx, m, before, to_left=False),
                                        comp2(ctx, m, before[0], face),
                                        rebracket(ctx, m, after, to_left=True)))
        assert infer(ctx, result)[2:] == (composite(ctx, m, before), composite(ctx, m, after))
        return new, result

    def route(state, swaps):
        order, moves = (0, 1, 2), []
        for pos in swaps:
            order, move = swap(state, order, pos)
            moves.append(move)
        assert order == (2, 1, 0)
        return composite(ctx, n, moves)

    # Strict activity on an edge changes exactly in its middle phase.
    for i in range(3):
        for state in product(range(4), repeat=3):
            if state[i] == 3:
                continue
            expected = {events[i][1]: 1} if state[i] == 1 else {}
            assert top_counts(ctx, edge(state, i)) == expected
    certify = certificate(emitter, ctx) if emitter else None
    for state in product(range(3), repeat=3):
        a, b = route(state, (0, 1, 0)), route(state, (1, 0, 1))
        h = fill(state, range(3), a, b)
        assert infer(ctx, h)[2:] == (a, b) and tdim_tm(ctx, h) == n + 2
        if certify and state == (0, 1, 2):
            certify('mixed-phase-braid', h, infer(ctx, h))
    refinement = block_refinement(ctx, m, events)
    if certify:
        certify('block-refinement', refinement, infer(ctx, refinement))
    print(f'Checked 144 typed edges with their activity and all 27 braid tiles at cut {d}; checked the two-entry block exchange.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('cut', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.cut < 1:
        parser.error('the three suspended branches need a positive cut')
    out = Emitter() if args.agda else None
    check(args.cut, out)
    if out:
        args.agda.write_text(out.module(args.agda.stem, 'A braid with three different phases.'))
