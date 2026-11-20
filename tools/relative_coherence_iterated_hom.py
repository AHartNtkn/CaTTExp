"""Check integer edge and relation columns at successive depths in a weak hom."""
from argparse import ArgumentParser
from pathlib import Path

from catt import STAR, arr, chain_tree, comp2, disc_tree, infer, maximal_vars, sub_from, subst_tm, tgt, tree_ctx, v
from ct_suspension import ident, susp_ctx, susp_tm
from emit_agda import Emitter
from gray_globe_branch_comparisons import cylinder
from relative_coherence_exchange_faces import head
from relative_coherence_hom_chains import boundary, hom_chain


def tower(ctx, value, height):
    for _ in range(height):
        value = ident(ctx, value)
    return value


def chart(rank, layers):
    # The first operation below the specified suspension layers has two branches.
    ctx = tree_ctx(chain_tree(2))
    x, y = (v(i) for i in maximal_vars(ctx))
    pole = tower(ctx, comp2(ctx, 0, x, y), rank-layers-2)
    cell = head(ctx, pole, pole)
    unit = ident(ctx, pole)
    out, back = head(ctx, cell, unit), head(ctx, unit, cell)
    for _ in range(layers):
        ctx = susp_ctx(ctx)
        cell, unit, out, back = map(susp_tm, (cell, unit, out, back))
    return ctx, cell, unit, out, back


def corner(layers, repeats):
    line = tree_ctx(disc_tree(1))
    ctx, minus, mix = cylinder(line, set(range(len(line))))
    point = minus[0]
    loop = v(len(ctx))
    ctx += (arr(STAR, point, point),)
    edge, square = minus[2], mix[2]
    for _ in range(repeats):
        edge = comp2(ctx, 0, loop, edge)
        square = comp2(ctx, 0, loop, square)
    if layers == 0:
        return ctx, (edge, mix[1])
    if layers == 1:
        return ctx, (square, ident(ctx, tgt(ctx, square)))
    label = tower(ctx, square, layers-1)
    return ctx, (label, label)


def verify(rank, layers, repeats, emitter=None):
    template, *generic = chart(rank, layers)
    ctx, labels = corner(layers, repeats)
    sigma = sub_from(template, ctx, dict(zip(maximal_vars(template), labels, strict=True)))
    cell, unit, out, back = (subst_tm(t, sigma) for t in generic)
    for depth in range(rank):
        assert hom_chain(ctx, cell, depth) == ({} if depth <= layers else {cell: 1})
        assert not hom_chain(ctx, unit, depth)
    for name, source, target, w, sign in [('out', cell, unit, out, -1), ('back', unit, cell, back, 1)]:
        assert infer(ctx, w) == arr(infer(ctx, source), source, target)
        for depth in range(rank):
            assert boundary(ctx, w, depth) == ({} if depth <= layers else {cell: sign})
        if emitter:
            emitter.check_type(name+str(layers), ctx, w, arr(infer(ctx, source), source, target))
        a, b, composite = source, target, w
        for k in range(1, 4):
            assert infer(ctx, composite) == arr(infer(ctx, a), a, b)
            assert boundary(ctx, composite, rank-1) == {cell: sign*k}
            if k < 3:
                a, b = comp2(ctx, rank-1, a, source), comp2(ctx, rank-1, b, target)
                composite = comp2(ctx, rank-1, composite, w)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--rank', type=int, default=5)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.rank < 4:
        parser.error('maximum rank must be at least four')
    emitter = Emitter() if args.agda else None
    count = 0
    for rank in range(4, args.rank+1):
        for layers in range(rank-1):
            for power in (0, 3):
                verify(rank, layers, power, emitter if rank == 4 and power == 0 else None)
                count += 1
    print(f'{count} labelled charts; all hom depths, both directions, and '
          f'{6*count} typed comparison powers.')
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Both unit-column orientations at all first-failure depths in rank four.'))
