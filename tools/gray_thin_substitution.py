"""Check the pure substitution folds and the mixed reverse-square paste of Response 21."""
from argparse import ArgumentParser
from pathlib import Path

from catt import (arr, comp2, infer, is_ps, maximal_vars, ps_dim, restrict, src,
                  subst_tm, tdim_tm, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_constant_cylinder import correction, whisk
from gray_globe_exterior_actions import certificate, chart_preimage, coherence
from gray_penultimate_partial_actions import data, distribute, rebracket
from gray_temporal_partial_actions import action, change_writing, rails
from gray_top_slot_promotion import support, top_action
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import composite, string_tree


def flat(ctx, term):
    shape, inclusion = restrict(ctx, support(ctx, term))
    assert is_ps(shape)
    recover = chart_preimage(shape, inclusion)
    if len(maximal_vars(shape)) == 1:
        point = inclusion[maximal_vars(shape)[0]]
        if infer(ctx, point) == infer(ctx, term):
            return point
    if ps_dim(shape) < tdim_tm(ctx, term) and src(ctx, term) == tgt(ctx, term):
        return ident(ctx, src(ctx, term))
    left, right = recover(src(ctx, term)), recover(tgt(ctx, term))
    assert left is not None and right is not None
    result = subst_tm(coherence(shape, left, right), inclusion)
    assert infer(ctx, result) == infer(ctx, term)
    assert top_counts(ctx, result) == top_counts(ctx, term)
    return result


def pure_fold(ctx, term, trace):
    """Normalize only same-rank arguments, then use the elementary root fold."""
    normal = flat(ctx, term)
    if normal == term:
        return None
    cut = tdim_tm(ctx, term)
    _, shape, ty, args = term
    promoted = {}
    labels = list(args)
    for i in maximal_vars(shape):
        if tdim_tm(shape, v(i)) == cut:
            step = pure_fold(ctx, args[i], trace)
            if step is not None:
                promoted[i] = step
                labels[i] = tgt(ctx, step)
    labels = tuple(labels)
    root = ('coh', shape, ty, labels)
    path = []
    if promoted:
        generic = ('coh', shape, ty, tuple(map(v, range(len(shape)))))
        path.append(top_action(shape, ctx, generic, (args, labels), promoted))
        assert (src(ctx, path[0]), tgt(ctx, path[0])) == (term, root)
    if root != normal:
        local, inclusion = restrict(ctx, support(ctx, root))
        recover = chart_preimage(local, inclusion)
        path.append(subst_tm(coherence(local, recover(root), recover(normal)), inclusion))
        trace.append((len(promoted), ps_dim(shape)))
    result = composite(ctx, cut, path)
    assert (src(ctx, result), tgt(ctx, result)) == (term, normal)
    assert not top_counts(ctx, result)
    return result


def cancel_at_side(old, ctx, copy, changes, side, a, b, vertical, expand):
    """Contract the padded cap loop next to a vertical arrow, or insert it."""
    base = src(old, a)
    assert tgt(old, b) == base
    k = tdim_tm(old, base)
    row = rails(old, base, changes, side)
    active = [(j, h) for j, h in enumerate(row) if h is not None]
    a0, b0 = (subst_tm(x, copy) for x in (a, b))
    pair = comp2(old, k, a, b)
    ends = (pair, ident(old, base))
    change = coherence(old, *(reversed(ends) if expand else ends))
    change = subst_tm(change, copy)
    for j, h in active:
        change = whisk(ctx, j, change, h, side)
    middle = whisk(ctx, k, change, vertical, side)
    outside = correction(ctx, subst_tm(base, copy), [*row, vertical], side, expand)
    dist = distribute(ctx, k, a0, b0, active, side, reverse=not expand)
    steps = [middle, outside]
    if dist is not None:
        steps.insert(0, whisk(ctx, k, dist, vertical, side))
    return composite(ctx, k+1, reversed(steps) if expand else steps)


def square_check(k, emitter):
    tree = string_tree(k-1, [k]*2)
    old = tree_ctx(tree)
    u = ucomp(old)
    vterm = comp2(old, k-1, ident(old, src(old, u)), u)
    # One exterior vertex moves, together with all its cofaces.
    marks = frozenset({0, *range(2, len(old))})
    ctx, copies, changes = data(old, marks)
    hu, actual, _ = action(tree, marks)
    assert ctx == actual and top_counts(ctx, hu)
    hv = change_writing(old, ctx, copies, changes, u, hu, vterm)
    p, q = coherence(old, u, vterm), coherence(old, vterm, u)
    q2 = comp2(old, k, q, ident(old, u))
    assert q != q2

    def cap(x, e):
        result = subst_tm(x, copies[e])
        for j, h in enumerate(rails(old, u, changes, e)):
            if h is not None:
                result = whisk(ctx, j, result, h, e)
        return result

    def product(x, y):
        return comp2(ctx, k, x, y)

    def adjust(steps, letters, end):
        last = tgt(ctx, steps[-1])
        step = rebracket(ctx, k, letters, last, end)
        if step is not None:
            steps.append(step)

    fp, gp, fq, fq2, gq2 = cap(p, 0), cap(p, 1), cap(q, 0), cap(q2, 0), cap(q2, 1)
    # Opposite of the given forward square, constructed here with actual terms.
    insert = cancel_at_side(old, ctx, copies[0], changes, 0, p, q, hu, True)
    steps = [product(insert, gp)]
    adjust(steps, [fp, fq, hu, gp], product(fp, hv))
    back = composite(ctx, k+1, steps)
    assert src(ctx, back) == product(hu, gp)

    # Reverse along q2, an independently written pure comparison.
    insert = cancel_at_side(old, ctx, copies[1], changes, 1, p, q2, hu, True)
    steps = [product(fq2, insert)]
    cross = product(product(fq2, back), gq2)
    adjust(steps, [fq2, hu, gp, gq2], src(ctx, cross))
    steps.append(cross)
    remove = cancel_at_side(old, ctx, copies[0], changes, 0, q2, p, hv, False)
    exit_step = product(remove, gq2)
    adjust(steps, [fq2, fp, hv, gq2], src(ctx, exit_step))
    steps.append(exit_step)
    result = composite(ctx, k+1, steps)
    start, end = product(fq2, hu), product(hv, gq2)
    wanted = arr(infer(ctx, start), start, end)
    assert infer(ctx, result) == wanted and not top_counts(ctx, result)
    if emitter:
        certificate(emitter, ctx)('reversed-thin-square', result, wanted)


def run(k, emitter):
    ctx = tree_ctx(string_tree(k-1, [k]*4))
    x, y, z, w = map(v, maximal_vars(ctx))
    def unit(t):
        return comp2(ctx, k-1, ident(ctx, src(ctx, t)), t)
    term = comp2(ctx, k-1, comp2(ctx, k-1, unit(x), y), comp2(ctx, k-1, z, unit(w)))
    other = comp2(ctx, k-1, x, comp2(ctx, k-1, y, comp2(ctx, k-1, z, w)))
    trace = []
    f, g = [pure_fold(ctx, t, trace) for t in (term, other)]
    assert tgt(ctx, f) == tgt(ctx, g) and max(n for n, _ in trace) == 2
    # Higher-identity inputs retain their actual, differently written poles.
    loop = coherence(ctx, term, other)
    higher = comp2(ctx, k, ident(ctx, term), loop)
    assert tgt(ctx, pure_fold(ctx, higher, trace)) == loop
    pointwise = ident(ctx, other)
    alternate = comp2(ctx, k, pointwise, pointwise)
    assert tgt(ctx, pure_fold(ctx, alternate, trace)) == pointwise
    square_check(k, emitter)
    print(f'Rank {k}: {len(trace)} pure folds and one mixed reverse square.', flush=True)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('rank', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.rank < 2:
        parser.error('rank must be at least two')
    out = Emitter() if args.agda else None
    for degree in range(2, args.rank+1):
        run(degree, out if degree == args.rank else None)
    if out:
        args.agda.write_text(out.module(args.agda.stem, 'Reversing a thin temporal comparison.'))
