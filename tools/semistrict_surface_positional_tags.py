"""Check positional lifts at repeated labels, compound top attachments and square cuts."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import (STAR, arr, chain_tree, check_ctx, comp2, comp_tree, glue_tree,
                  infer, maximal_vars, sub_from, subst_tm, subst_ty, tdim, tgt, tree_ctx, v)
from catt_unit_ordered_exchange import temporal_words
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_hidden_seam import identity


def loop_tower(height):
    ctx = (STAR,)
    for dim in range(1, height + 1):
        pole = v(dim - 1)
        ctx += (arr(infer(ctx, pole), pole, pole),)
    return ctx


def attachment(rank, emitter):
    lower = rank - 1
    tree = string_tree(lower - 1, [lower] * 3)
    row = tree_ctx(tree)
    a, b, c = map(v, maximal_vars(row))
    left = comp2(row, lower - 1, comp2(row, lower - 1, a, b), c)
    right = comp2(row, lower - 1, a, comp2(row, lower - 1, b, c))
    compare = head(row, right, left)
    ctx = loop_tower(lower)
    k = v(len(ctx))
    ctx += (infer(ctx, v(lower)),)
    fold = sub_from(row, ctx, {i: v(lower) for i in maximal_vars(row)})
    source, other, track = (subst_tm(t, fold) for t in (left, right, compare))
    z = v(len(ctx))
    ctx += (arr(infer(ctx, source), source, k),)
    check_ctx(ctx)
    old = arr(infer(ctx, other), other, k)
    assert infer(ctx, z) != old
    fit = comp2(ctx, lower, track, z)
    assert infer(ctx, fit) == old
    emitter.check_type(f'fitted{rank}', ctx, fit, old)


def check_cut(left_changes, right_changes, gap, emitter):
    square = tree_ctx(glue_tree(2, 0, 2))
    a, b = map(v, maximal_vars(square))
    chart = tree_ctx(((chain_tree(left_changes),),) + ((),) * gap + ((chain_tree(right_changes),),))
    dims = [tdim(t) + 1 for t in chart]
    two = [i for i, d in enumerate(dims) if d == 2]
    first_right = two[left_changes + 1]
    tips = maximal_vars(chart)
    edges = [i for i in tips if dims[i] == 1]
    assert len(edges) == gap
    mid_vertex = tgt(square, tgt(square, a))
    images = {}
    for i in tips:
        event = a if i < first_right else b
        if dims[i] == 1:
            images[i] = identity(square, mid_vertex)
        elif dims[i] == 2:
            images[i] = event
        else:
            images[i] = identity(square, event)
    clamp = sub_from(chart, square, images)
    tower = loop_tower(3)
    fold = tuple(v(dim) for dim in dims)
    for ctx, sigma in ((square, clamp), (tower, fold)):
        assert all(infer(ctx, image) == subst_ty(ty, sigma)
                   for image, ty in zip(sigma, chart, strict=True))
    middle = comp_tree(chain_tree(gap), chart, list(map(v, edges))) if edges else None
    rows = [set(), set()]
    collapsed = [set(), set()]
    count = 0
    for l, r in product(two[:left_changes + 1], two[left_changes + 1:]):
        first = v(l) if middle is None else comp2(chart, 0, v(l), middle)
        for index, term in enumerate(temporal_words(chart, first, v(r), 0, 1)):
            rows[index].add(subst_tm(term, fold))
            collapsed[index].add(subst_tm(term, clamp))
        count += 1
    assert all(len(xs) == 1 for xs in rows + collapsed)
    assert rows[0] != rows[1]
    early, late = (next(iter(xs)) for xs in collapsed)
    assert infer(square, early) == infer(square, late) and early != late
    if (left_changes, right_changes, gap) == (2, 1, 2):
        typ = infer(square, early)
        for label, start, end, expected in [('forward', late, early, 'true'),
                                            ('reverse', early, late, 'false')]:
            emitter.checks.append(
                f'{label} : graySide {emitter.ctx(square)} {emitter.ty(typ)} '
                f'{emitter.tm(start)} {emitter.tm(end)} ≡ {expected}\n{label} = refl\n')
        for cut in range(3):
            ct, cy = emitter.ctx(chart), emitter.ctx(square)
            emitter.checks.append(
                f'clamp{cut} : {cy} ⊢sub {emitter.sub(clamp)} ∶ {ct}\n'
                f'clamp{cut} = from-just (checkSub {cy} (from-just (checkCtx {cy})) '
                f'{emitter.sub(clamp)} {ct})\n')
            chart, square = susp_ctx(chart), susp_ctx(square)
            clamp = (v(0), v(1)) + tuple(map(susp_tm, clamp))
    return count


def check_interchange_tag(emitter):
    """A directed tag can project to a Gray identity before any tip is pruned."""
    square = tree_ctx(glue_tree(2, 0, 2))
    residual = tree_ctx(glue_tree(2, 0, 1))
    a, b = maximal_vars(square)
    event, edge = map(v, maximal_vars(residual))
    prune = sub_from(square, residual, {a: event, b: identity(residual, edge)})
    early, late = temporal_words(square, v(a), v(b), 0, 1)
    for cut in range(3):
        ty = infer(square, late)
        assert early != late and infer(square, early) == ty
        for pred, expected in [('cohCase', cut > 0), ('graySide', True)]:
            name = f'tag{cut}{pred}'
            emitter.checks.append(
                f'{name} : {pred} {emitter.ctx(square)} {emitter.ty(ty)} '
                f'{emitter.tm(late)} {emitter.tm(early)} ≡ {str(expected).lower()}\n{name} = refl\n')
        forward = subst_tm(head(square, late, early), prune)
        outside = (subst_tm(late, prune), subst_tm(early, prune))
        emitter.check_type(f'prunedTag{cut}', residual, forward,
                           arr(infer(residual, outside[0]), *outside))
        square, residual = susp_ctx(square), susp_ctx(residual)
        early, late = susp_tm(early), susp_tm(late)
        prune = (v(0), v(1)) + tuple(map(susp_tm, prune))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    count = sum(check_cut(left, right, gap, emitter)
                for left, right, gap in product(range(4), range(4), range(3)))
    for rank in range(3, 7):
        attachment(rank, emitter)
    check_interchange_tag(emitter)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = 'PositionalTagChecks'
        source = emitter.module(module, __doc__)
        (args.agda_dir / (module + '.agda')).write_text(
            source.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))
    print(f'Checked {count} pairs of phase choices in 48 charts, and fitted attachments through degree six.')


if __name__ == '__main__':
    main()
