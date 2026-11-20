"""Construct the two sides of the mixed equation for either walking cancellation."""
from argparse import ArgumentParser
from pathlib import Path

from catt import (arr, check_ctx, comp2, disc_tree, fv_tm, fv_ty, glue_tree, infer,
                  maximal_vars, src, sub_from, subst_tm, subst_ty, tgt, tree_ctx, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_constant_cylinder import correction
from gray_globe_branch_comparisons import cylinder
from gray_partial_cylinder_sections import selections
from gray_temporal_partial_actions import action, pad, rails
from relative_coherence_cut import top_counts


def binary_change(tree, old, inputs, marks, copies, changes):
    chart = tree_ctx(tree)
    labels = sub_from(chart, old, dict(zip(maximal_vars(chart), inputs, strict=True)))
    selected = frozenset(i for i, label in enumerate(labels) if label[1] in marks)
    term, domain, _ = action(tree, selected)
    sigma = []
    for i, label in enumerate(labels):
        j = label[1]
        sigma.append(copies[0][j])
        if i in selected:
            sigma.extend((copies[1][j], changes[j]))
    assert len(sigma) == len(domain)
    return subst_tm(term, sigma)


def cancellation(n, old, f, b, marks, inverse_first, emitter, label):
    ctx, minus, changes = cylinder(old, marks)
    plus = [v(m[1]+1) if i in marks else m for i, m in enumerate(minus)]
    copies = minus, plus
    pair = (b, f) if inverse_first else (f, b)
    composite = comp2(old, n-1, *pair)
    z = src(old, composite)
    assert z == tgt(old, composite)
    unit = ident(old, z)
    ty = arr(infer(old, unit), composite, unit)
    theta = v(len(ctx)), v(len(ctx)+1)
    ctx += tuple(subst_ty(ty, copy) for copy in copies)

    mixed_composite = binary_change(glue_tree(n, n-1, n), old, pair, marks, copies, changes)
    cap = [pad(ctx, old, composite, changes, side)(subst_tm(composite, copy))
           for side, copy in enumerate(copies)]
    assert infer(ctx, mixed_composite) == arr(infer(ctx, cap[0]), *cap)
    sides = [pad(ctx, old, composite, changes, side)(theta[side]) for side in (0, 1)]
    if z[1] in marks:
        steps = [correction(ctx, copy[z[1]], rails(old, unit, changes, side), side, bool(side))
                 for side, copy in enumerate(copies)]
        mixed_unit = comp2(ctx, n, *steps)
        sides[0] = comp2(ctx, n, sides[0], mixed_unit)
    sides[1] = comp2(ctx, n, mixed_composite, sides[1])
    expected = infer(ctx, sides[0])
    assert infer(ctx, sides[1]) == expected
    slot = changes[b[1]][1]
    assert slot not in fv_ty(expected) and slot not in fv_tm(sides[0])
    assert top_counts(ctx, sides[1])[slot] == 1
    check_ctx(ctx)
    if emitter:
        for side, term in enumerate(sides):
            emitter.check_type(f'cap{label}side{side}', ctx, term, expected)


def run(height, destination):
    emitter = Emitter() if destination else None
    for n in range(1, height+1):
        globe = tree_ctx(disc_tree(n))
        f = v(maximal_vars(globe)[0])
        b = v(len(globe))
        ty = infer(globe, f)
        old = globe + (arr(ty[1], ty[3], ty[2]),)
        count = 0
        for marks in selections(old):
            if f[1] not in marks or b[1] not in marks:
                continue
            for inverse_first in (False, True):
                count += 1
                cancellation(n, old, f, b, marks, inverse_first,
                             emitter if n <= 2 else None, f'{n}case{count}')
        print(f'Rank {n}: {count} typed single-input equations', flush=True)
    if emitter:
        destination.write_text(emitter.module(destination.stem, 'Walking inverse component equations.'))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('height', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.height < 1:
        parser.error('expected a positive height')
    run(args.height, args.agda)
