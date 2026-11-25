"""Check native inner subdivisions on a two-column tree with only generating 2-cells."""
from argparse import ArgumentParser
from functools import cache
from pathlib import Path

from catt import comp2, fv_tm, fv_ty, infer, maximal_vars, src, subst_tm, tdim, tdim_tm, tgt, v
from ct_suspension import susp_tm
from relative_coherence_exchange_faces import composite
from semistrict_surface_directed_power_queries import chart, crossing, row_fit, square
from semistrict_surface_inverse_completion import DerivationEmitter
from semistrict_surface_positional_tags import loop_tower
from semistrict_surface_thin_subdivision import partition_route


def marked_inputs(size, split_left):
    ctx = chart(2, size + 1)
    tips = list(map(v, maximal_vars(ctx)))
    left, right = tips[:2], tips[2:]
    if split_left:
        a, single = left
        block, partner = right[:-1], right[-1]
    else:
        single, a = left
        partner, block = right[0], right[1:]
    g = crossing(ctx, single, partner)
    changes = []
    for i in reversed(range(size)):
        before = [comp2(ctx, 0, src(ctx, a), z) for z in block[:i]]
        after = [comp2(ctx, 0, tgt(ctx, a), z) for z in block[i + 1:]]
        step = composite(ctx, 1, [*before, crossing(ctx, a, block[i]), *after])
        if changes and (end := tgt(ctx, changes[-1])) != src(ctx, step):
            step = comp2(ctx, 2, row_fit(ctx, end, src(ctx, step)), step)
        changes.append(step)
    inputs = changes + [g] if split_left else [g] + changes
    return ctx, inputs, [(a, b) for b in reversed(block)], (single, partner), left, right


def check_shuffle(left, right, block_pairs, single, split_left):
    a = block_pairs[0][0]
    bs = [b for _, b in reversed(block_pairs)]
    f_start, f_end = [*bs, a], [a, *bs]
    g_start, g_end = list(reversed(single)), list(single)
    start, end = ((f_start + g_start, f_end + g_end) if split_left else
                  (g_start + f_start, g_end + f_end))
    allowed = set(block_pairs) | {single}
    positions = {x: i for i, x in enumerate(end)}
    histories = []

    def walk(state, history):
        if state == end:
            histories.append(history)
        for i, (b, a) in enumerate(zip(state, state[1:])):
            if b in right and a in left and positions[b] > positions[a]:
                walk(state[:i] + [a, b] + state[i + 2:], [*history, (a, b)])
    walk(start, [])
    assert len(histories) == len(bs) + 1
    assert all(set(h) == allowed and [pair for pair in h if pair != single] == block_pairs for h in histories)

    # An active degree-one interval on each side contributes their whole tensor support.
    for left_mask in range(1, 1 << len(left)):
        for right_mask in range(1, 1 << len(right)):
            mixed = {(a, b) for i, a in enumerate(left) for j, b in enumerate(right)
                     if left_mask & (1 << i) and right_mask & (1 << j)}
            if mixed <= allowed:
                assert single not in mixed or mixed.isdisjoint(block_pairs)


def check_routes(size, split_left, emitter):
    ctx, inputs, changes, single, left, right = marked_inputs(size, split_left)
    check_shuffle(left, right, changes, single, split_left)
    outer, chi = square(2)
    inner = susp_tm(chi)

    @cache
    def marks(t):
        if t[0] == 'v':
            return frozenset()
        _, arity, ty, labels = t
        tips = maximal_vars(arity)
        if (arity, ty) == (outer, chi[2]):
            return frozenset({tuple(labels[i] for i in tips)})
        return frozenset().union(*(marks(labels[i]) for i in tips if tdim_tm(ctx, labels[i]) == 3))

    def exchanges(t):
        _, arity, ty, labels = t
        tips = maximal_vars(arity)
        if (arity, ty) == (inner[1], inner[2]):
            a, b = [marks(labels[i]) for i in tips]
            return [(a, b) if split_left else (b, a)]
        return [pair for i in tips if tdim_tm(ctx, labels[i]) == 4 for pair in exchanges(labels[i])]

    direct = partition_route(ctx, inputs, size, (size,), split_left)
    tower = loop_tower(2)
    fold = tuple(v(tdim(ty) + 1) for ty in ctx)
    folded_type = infer(tower, subst_tm(direct, fold))
    folded_faces = set()
    for mask in range(1 << (size - 1)):
        cuts = tuple(i for i in range(1, size) if mask & (1 << (i - 1))) + (size,)
        route = partition_route(ctx, inputs, size, cuts, split_left)
        pairs = exchanges(route)
        expected = {frozenset(changes[lo:hi]) for lo, hi in zip((0, *cuts[:-1]), cuts, strict=True)}
        assert all(partner == {single} for _, partner in pairs)
        assert {block for block, _ in pairs} == expected and len(pairs) == len(expected)
        assert infer(ctx, route) == infer(ctx, direct)
        assert set(fv_tm(route)) | set(fv_ty(infer(ctx, route))) == set(range(len(ctx)))
        folded = subst_tm(route, fold)
        assert infer(tower, folded) == folded_type
        folded_faces.add(folded)
    assert len(folded_faces) == 1 << (size - 1)
    if emitter is not None and size == 2:
        side = 'first' if split_left else 'second'
        emitter.check_type(side + 'Direct', ctx, direct, infer(ctx, route))
        emitter.check_type(side + 'Pasted', ctx, route, infer(ctx, direct))
        emitter.checks.append(f'{side}FullHead : cohCase {emitter.ctx(ctx)} {emitter.ty(infer(ctx, direct))} '
                              f'{emitter.tm(direct)} {emitter.tm(route)} ≡ false\n{side}FullHead = refl\n')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = DerivationEmitter() if args.agda_dir else None
    for size in range(2, 6):
        for split_left in (True, False):
            check_routes(size, split_left, emitter)
    if emitter:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        source = emitter.module('RectangleSubdivision', __doc__).replace(
            'open import CaTTExp.Pure\n', 'open import CaTTExp.Gray.Pure\n'
            'open import CaTTExp.Pure using (∅)\n'
            'open import CaTTExp.PastingCheck ∅ using () renaming (checkPs to pastable)\n')
        (args.agda_dir / 'RectangleSubdivision.agda').write_text(source)
    print('Checked 60 old four-dimensional routes on rectangles and their three-declaration folds.')


if __name__ == '__main__':
    main()
