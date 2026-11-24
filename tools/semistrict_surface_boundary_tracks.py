"""Check raw frame preimages and fit two changes through overlapping path bracketings."""
from argparse import ArgumentParser
from functools import lru_cache
from itertools import product
from pathlib import Path

from catt import (STAR, arr, comp2, infer, maximal_vars, src, sub_from, subst_tm,
                  subst_ty, tgt, tree_ctx, v)
from ct_suspension import ident, susp_ctx, susp_tm, susp_ty
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from semistrict_surface_globular_balance_matching import boundary_head, product_at, verify_class


def inverse_terms(chart, label):
    """Compute literal term preimages, including variable and head readings."""
    @lru_cache(None)
    def terms(target):
        answers = [v(i) for i, image in enumerate(label) if image == target]
        if target[0] == 'coh':
            _, shape, generic, inputs = target
            partials = [()]
            for local_type, image in zip(shape, inputs, strict=True):
                partials = [prefix + (entry,) for prefix in partials for entry in terms(image)
                            if infer(chart, entry) == subst_ty(local_type, prefix)]
            answers.extend(('coh', shape, generic, entries) for entries in partials)
        return tuple(answers)

    return terms


def preimages(chart, label, target_type):
    """All literally typed preimages. Generic coherence types are bound syntax."""
    terms = inverse_terms(chart, label)

    def types(ty):
        if ty == STAR:
            return (STAR,)
        _, base, lo, hi = ty
        return tuple(arr(a, s, t) for a, s, t in product(types(base), terms(lo), terms(hi))
                     if infer(chart, s) == a == infer(chart, t))

    return types(target_type)


def pattern(dimensions):
    ctx = tree_ctx(string_tree(0, dimensions))
    return ctx, tuple(v(i) for i in maximal_vars(ctx))


def specialize(chart, context, images):
    return sub_from(chart, context, dict(zip(maximal_vars(chart), images, strict=True)))


def bracket(ctx, terms, side):
    a, b, c = terms
    if side == 'left':
        return comp2(ctx, 0, comp2(ctx, 0, a, b), c)
    if side == 'right':
        return comp2(ctx, 0, a, comp2(ctx, 0, b, c))
    return product_at(ctx, 0, *terms)


def example(binary, agda_dir):
    row, edges = pattern([1, 1, 1])
    f, g, h = edges
    fg, gh = comp2(row, 0, f, g), comp2(row, 0, g, h)
    paths = {s: bracket(row, edges, s) for s in ('left', 'right', 'fine')}
    tracks = {s: (head(row, paths['fine'], paths[s]), head(row, paths[s], paths['fine']))
              for s in ('left', 'right')}

    def endo(ctx, t):
        return arr(infer(ctx, t), t, t)

    ctx = (*row, endo(row, g), endo(row, fg), endo(row, gh))
    z, x, y = (v(len(row) + i) for i in range(3))
    p_ty = arr(infer(ctx, x), x, comp2(ctx, 0, f, z))
    q_ty = arr(infer(ctx, y), comp2(ctx, 0, z, h), y)
    p, q = v(len(ctx)), v(len(ctx) + 1)
    ctx += (p_ty, q_ty)
    steps = [comp2(ctx, 0, p, h), comp2(ctx, 0, f, q)]
    fit = [product_at(ctx, 1, start, step, end) for step, (start, end) in zip(steps, tracks.values(), strict=True)]

    # A free central bigon has distinct signed edges. Build the comparison
    # before identifying them, so that its generic support is the whole tree.
    mid, slots = pattern([1, 2, 1])
    faces = []
    for side in ('left', 'right'):
        core = bracket(mid, slots, side)
        fine = bracket(mid, slots, 'fine')
        start = boundary_head(mid, 1, '-', src(mid, fine), src(mid, core))
        end = boundary_head(mid, 1, '+', tgt(mid, core), tgt(mid, fine))
        faces.append(product_at(mid, 1, start, core, end))
    join = subst_tm(head(mid, *faces), specialize(mid, ctx, (f, z, h)))
    assert src(ctx, join) == tgt(ctx, fit[0]) and tgt(ctx, join) == src(ctx, fit[1])
    witness = product_at(ctx, 2, fit[0], join, fit[1])
    old = arr(infer(ctx, src(ctx, fit[0])), src(ctx, fit[0]), tgt(ctx, fit[1]))
    assert old[1] == endo(ctx, paths['fine']) and infer(ctx, witness) == old

    charts = []
    for dims, images, side in (([3, 1], (p, h), 'left'), ([1, 3], (f, q), 'right')):
        chart, _ = pattern(dims)
        label = specialize(chart, ctx, images)
        charts.append((chart, label, endo(ctx, paths[side])))
    emitter = Emitter() if agda_dir else None
    for cut in range(3):
        for chart, label, local_image in charts:
            assert not preimages(chart, label, old[1])
            possible = preimages(chart, label, local_image)
            assert possible and all(subst_ty(a, label) == local_image for a in possible)
        assert infer(ctx, witness) == old
        verify_class(binary, ctx, steps, witness, old, cut + 3)
        if emitter:
            emitter.check_typed(f'fit{cut}', ctx, witness)
            emitter.check_type(f'fit{cut}', ctx, witness, old)
        if cut < 2:
            ctx = susp_ctx(ctx)
            steps = list(map(susp_tm, steps))
            witness, old = susp_tm(witness), susp_ty(old)
            charts = [(susp_ctx(chart), (v(0), v(1), *map(susp_tm, label)), susp_ty(local_image))
                      for chart, label, local_image in charts]
    if emitter:
        agda_dir.mkdir(parents=True, exist_ok=True)
        (agda_dir / 'BoundaryTracks.agda').write_text(emitter.module('BoundaryTracks', __doc__))


def closed_tracks(binary, agda_dir):
    row, edges = pattern([1, 1, 1])
    f, g, h = edges
    fg = comp2(row, 0, f, g)
    left, right = (bracket(row, edges, side) for side in ('left', 'right'))
    lr, rl = head(row, left, right), head(row, right, left)
    endo = lambda ctx, t: arr(infer(ctx, t), t, t)
    ctx = (*row, endo(row, g), endo(row, g), endo(row, fg), endo(row, fg))
    z0, z1, x, y = (v(len(row) + i) for i in range(4))
    p, q, r = (v(len(ctx) + i) for i in range(3))
    a, b = comp2(ctx, 0, z0, h), comp2(ctx, 0, z1, h)
    ctx += (arr(infer(ctx, x), x, comp2(ctx, 0, f, z0)), arr(infer(ctx, a), a, b),
            arr(infer(ctx, y), comp2(ctx, 0, f, z1), y))
    steps = [comp2(ctx, 0, p, h), comp2(ctx, 0, f, q), comp2(ctx, 0, r, h)]

    mid, slots = pattern([1, 2, 1])
    slab = steps[0]
    for start_side, end_side, event, back, fwd, step in (
            ('left', 'right', z0, rl, lr, steps[1]), ('right', 'left', z1, lr, rl, steps[2])):
        before, after = (bracket(mid, slots, side) for side in (start_side, end_side))
        pre = boundary_head(mid, 1, '-', src(mid, after), src(mid, before))
        post = boundary_head(mid, 1, '+', tgt(mid, before), tgt(mid, after))
        bridge = head(mid, product_at(mid, 1, pre, before, post), after)
        bridge = subst_tm(bridge, specialize(mid, ctx, (f, event, h)))
        slab = product_at(ctx, 2, product_at(ctx, 1, back, slab, fwd), bridge, step)

    # Close each loop in the fine edge row, then place these fillings on
    # opposite sides of the initial 2-cell at the temporal 1-cut.
    loop = comp2(row, 1, lr, rl)
    disk = head(row, ident(row, left), loop)
    start = src(ctx, steps[0])
    expand = product_at(ctx, 1, disk, start, disk)
    globe, (cell,) = pattern([2])
    unitors = head(globe, cell, product_at(globe, 1, ident(globe, src(globe, cell)),
                                           cell, ident(globe, tgt(globe, cell))))
    enter = subst_tm(unitors, specialize(globe, ctx, (start,)))
    vertical = tree_ctx(string_tree(1, [2] * 5))
    i, j, u, v1, w = (v(k) for k in maximal_vars(vertical))
    flat = product_at(vertical, 1, comp2(vertical, 1, i, j), u, comp2(vertical, 1, v1, w))
    nested = product_at(vertical, 1, i, product_at(vertical, 1, j, u, v1), w)
    reassoc = subst_tm(head(vertical, flat, nested), specialize(vertical, ctx, (lr, rl, start, lr, rl)))
    witness = product_at(ctx, 2, enter, expand, reassoc, slab)
    old = arr(infer(ctx, start), start, tgt(ctx, steps[-1]))
    assert infer(ctx, witness) == old
    emitter = Emitter() if agda_dir else None
    for cut in range(3):
        verify_class(binary, ctx, steps, witness, old, cut + 3)
        if emitter:
            emitter.check_typed(f'closed{cut}', ctx, witness)
            emitter.check_type(f'closed{cut}', ctx, witness, old)
        if cut < 2:
            ctx, witness, old = susp_ctx(ctx), susp_tm(witness), susp_ty(old)
            steps = list(map(susp_tm, steps))
    if emitter:
        (agda_dir / 'ClosedBoundaryTracks.agda').write_text(emitter.module('ClosedBoundaryTracks', __doc__))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--rice-binary', required=True, type=Path)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    example(args.rice_binary.resolve(), args.agda_dir)
    closed_tracks(args.rice_binary.resolve(), args.agda_dir)
    print('Verified raw frame preimages, prescribed boundaries and surface classes in degrees 3, 4 and 5.')
