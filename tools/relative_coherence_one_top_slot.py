"""Factor a marked top slot into elementary whiskerings with literal boundary pads."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import (arr, comp2, fv_tm, fv_ty, glue_tree, infer, maximal_vars, restrict,
                  subst_tm, tdim, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head


def carried_pad(ctx, source, target):
    ty = infer(ctx, source)
    assert ty == infer(ctx, target)
    support = fv_tm(source) | fv_ty(ty)
    assert support == fv_tm(target) | fv_ty(ty)
    small, incl = restrict(ctx, support)
    back = [None] * len(ctx)
    for i, variable in enumerate(incl):
        back[variable[1]] = v(i)
    return subst_tm(head(small, subst_tm(source, back), subst_tm(target, back)), incl)


def lower_face(ctx, term, degree, sign):
    ty = infer(ctx, term)
    while tdim(ty) > degree:
        ty = ty[1]
    return ty[sign]


def check(d, p, cut, right, emitter):
    heights = (p, d) if right else (d, p)
    chart = tree_ctx(glue_tree(heights[0], cut, heights[1]))
    l, r = map(v, maximal_vars(chart))
    x = r if right else l
    whole = comp2(chart, cut, l, r)
    src = lower_face(chart, r, p - 1, 2)
    tgt = lower_face(chart, l, p - 1, 3)
    split = comp2(chart, p - 1, comp2(chart, cut, l, src), comp2(chart, cut, tgt, r))
    ty = infer(chart, whole)
    count = 0
    for level in range(1, d):
        for sign in (2, 3):
            actual = lower_face(chart, split, level, sign)
            desired = lower_face(chart, whole, level, sign)
            if actual != desired:
                s, t = (desired, actual) if sign == 2 else (actual, desired)
                pad = carried_pad(chart, s, t)
                assert x[1] not in fv_tm(pad)
                split = (comp2(chart, level, pad, split) if sign == 2
                         else comp2(chart, level, split, pad))
                count += 1
    assert infer(chart, split) == ty
    assert top_counts(chart, split)[x[1]] == top_counts(chart, whole)[x[1]] == 1
    for label, source, target in (('factor', whole, split), ('collect', split, whole)):
        proof = head(chart, source, target)
        expected = arr(ty, source, target)
        assert infer(chart, proof) == expected
        if emitter:
            emitter.check_type(label + str(d) + str(p) + str(cut) + ('R' if right else 'L'),
                               chart, proof, expected)
    return count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    for d in range(2, 5):
        positions = [(p, cut) for p in range(2, d + 1) for cut in range(p - 1)]
        total = sum(check(d, p, cut, right, emitter)
                    for (p, cut), right in product(positions, (False, True)))
        print(f'Rank {d}: {2 * len(positions)} non-elementary positions, {total} boundary pads, '
              'two typed comparisons per position.')
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Elementary whisker factorizations on a marked slot.'))
