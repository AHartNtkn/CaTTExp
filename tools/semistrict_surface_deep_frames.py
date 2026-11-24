"""Fit an old composite with differently bracketed boundaries at every positive rank."""
from argparse import ArgumentParser
from pathlib import Path

from catt import arr, comp2, infer, src, subst_tm, tdim_tm, tgt, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from semistrict_surface_boundary_tracks import bracket, pattern, preimages, specialize
from semistrict_surface_chart_pullback import ChartPullback, check_path_charts, folded_edges, frame_path, mixed_leg, type_equality
from semistrict_surface_globular_balance_matching import boundary_head, product_at, verify_class


def face(ctx, cell, degree, sign):
    take = src if sign == '-' else tgt
    while tdim_tm(ctx, cell) > degree:
        cell = take(ctx, cell)
    return cell


def deep_chain(rank, binary, agda_dir):
    mid, slots = pattern([1, rank, 1])
    f, z0, h = slots
    left = bracket(mid, slots, 'left')
    right = bracket(mid, slots, 'right')
    tracks = []
    for j in range(1, rank):
        assert all(face(mid, left, j, s) != face(mid, right, j, s) for s in ('-', '+'))
        pre = boundary_head(mid, j, '-', face(mid, left, j, '-'), face(mid, right, j, '-'))
        post = boundary_head(mid, j, '+', face(mid, right, j, '+'), face(mid, left, j, '+'))
        tracks.append((pre, post))
        right = product_at(mid, j, pre, right, post)
    assert infer(mid, left) == infer(mid, right)
    enter, leave = head(mid, left, right), head(mid, right, left)

    z1, x, y = (v(len(mid) + i) for i in range(3))
    inner_type = infer(mid, comp2(mid, 0, f, z0))
    ctx = (*mid, infer(mid, z0), inner_type, inner_type)
    p, q, s = (v(len(ctx) + i) for i in range(3))
    pre_q, post_q = comp2(ctx, 0, z0, h), comp2(ctx, 0, z1, h)
    ctx += (arr(inner_type, x, comp2(ctx, 0, f, z0)), arr(infer(ctx, pre_q), pre_q, post_q),
            arr(inner_type, comp2(ctx, 0, f, z1), y))
    steps = (comp2(ctx, 0, p, h), comp2(ctx, 0, f, q), comp2(ctx, 0, s, h))
    first = specialize(mid, ctx, (f, z0, h))
    last = specialize(mid, ctx, (f, z1, h))
    common = ChartPullback((mid, first), (mid, last))
    coarse_type = infer(mid, bracket(mid, slots, 'right'))
    target = infer(mid, left)
    same = type_equality(binary, rank)
    assert frame_path(((mid, first), (mid, last)), ((target,), (target,)),
                      ((coarse_type, coarse_type),), same) == (target, target)
    for pre, post in tracks:
        for t in (pre, post):
            lift = common.pair_term(t, t)
            infer(common.ctx, lift)
            assert tuple(subst_tm(lift, p) for p in common.projections) == (t, t)
    fitted = steps[1]
    for j, pair in enumerate(tracks, 1):
        pre, post = (subst_tm(t, first) for t in pair)
        assert (pre, post) == tuple(subst_tm(t, last) for t in pair)
        fitted = product_at(ctx, j, pre, fitted, post)
    witness = product_at(ctx, rank, steps[0], subst_tm(enter, first), fitted, subst_tm(leave, last), steps[-1])
    old = arr(infer(ctx, src(ctx, steps[0])), src(ctx, steps[0]), tgt(ctx, steps[-1]))
    assert infer(ctx, witness) == old
    # At the central coarse step the entire written frame fails to pull back,
    # already because its path level is the opposite binary bracketing.
    coarse, _ = pattern([1, rank + 1])
    label = specialize(coarse, ctx, (f, q))
    assert not preimages(coarse, label, old[1])
    assert all(face(ctx, tgt(ctx, steps[0]), j, sign) != face(ctx, src(ctx, steps[1]), j, sign)
               for j in range(1, rank) for sign in ('-', '+'))
    verify_class(binary, ctx, steps, witness, old, rank + 1, width=rank)
    if agda_dir:
        emitter = Emitter()
        name = f'DeepFrames{rank}'
        emitter.check_typed('fitted', ctx, witness)
        emitter.check_type('fitted', ctx, witness, old)
        agda_dir.mkdir(parents=True, exist_ok=True)
        (agda_dir / (name + '.agda')).write_text(emitter.module(name, __doc__))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--rice-binary', required=True, type=Path)
    parser.add_argument('--agda-dir', type=Path)
    parser.add_argument('--rank', action='append', type=int)
    args = parser.parse_args()
    count, pairs, positive = check_path_charts()
    print(f'Checked {count} pullbacks, {pairs} matched readings and {positive} positive path tests.', flush=True)
    folded_edges(args.rice_binary.resolve())
    for rank in args.rank or (2, 3, 4, 5):
        if rank < 2:
            parser.error('rank must be at least two')
        mixed_leg(rank, args.rice_binary.resolve())
        deep_chain(rank, args.rice_binary.resolve(), args.agda_dir)
        print(f'Degree {rank + 1}: checked {rank - 1} mismatching boundary ranks and width {rank}.', flush=True)
