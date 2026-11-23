"""Unfold object identifications on terms with composite and identity attachments."""

from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, subst_tm, subst_ty, v
from emit_agda import Emitter
from relative_coherence_cut import outer_edge
from relative_coherence_hidden_seam import identity
from semistrict_surface_path_lift import columns


def reduce_path(*parts):
    result = []
    for part in parts:
        for edge in part:
            if result and result[-1] == -edge:
                result.pop()
            else:
                result.append(edge)
    return tuple(result)


def presentation():
    ctx = [STAR] * 3

    def variable(ty):
        x = v(len(ctx))
        ctx.append(ty)
        return x

    f, g, k, h = [variable(arr(STAR, v(i), v(j)))
                  for i, j in ((0, 1), (1, 2), (0, 2), (2, 2))]
    fg = comp2(tuple(ctx), 0, f, g)
    a = variable(arr(infer(tuple(ctx), k), fg, k))
    iy, iz = (identity(tuple(ctx), v(i)) for i in (1, 2))
    s = variable(arr(infer(tuple(ctx), iy), iy, iy))
    b = variable(arr(infer(tuple(ctx), iz), iz, h))
    p = variable(arr(infer(tuple(ctx), a), a, a))
    q = variable(arr(infer(tuple(ctx), b), b, b))
    check_ctx(tuple(ctx))
    return tuple(ctx), (f, g, k, h, a, s, b, p, q)


def check_lifts():
    ctx, variables = presentation()
    point = (STAR,)
    folded = [STAR]
    fold = [v(0)] * 3
    point_labels = fold.copy()
    for ty in ctx[3:]:
        fold.append(v(len(folded)))
        folded.append(subst_ty(ty, fold[:-1]))
        point_labels.append(('coh', point, subst_ty(ty, point_labels), (v(0),)))
    folded, fold, point_labels = tuple(folded), tuple(fold), tuple(point_labels)
    check_ctx(folded)
    for term, ty in zip(point_labels, ctx):
        assert infer(point, term) == subst_ty(ty, point_labels)
    f, g, k, h, a, s, b, p, q = [subst_tm(t, fold) for t in variables]
    old_of = {fold[i]: i for i in range(3, len(ctx))}

    @cache
    def grade(t):
        if t == v(0):
            return ()
        if t[0] == 'v':
            i, j = outer_edge(ctx[old_of[t]])
            return reduce_path((-(i + 1), j + 1))
        return reduce_path(*(grade(t[3][i]) for i in columns(t[1])[1]))

    def walk(t, sheet, on_var):
        if t[0] == 'v':
            if t == v(0):
                return on_var(None, sheet)
            index = old_of[t]
            i, _ = outer_edge(ctx[index])
            return on_var(index, reduce_path(sheet, (-(i + 1),)))
        _, arity, ty, args = t
        slots, arrows = columns(arity)
        ends = [sheet]
        for i in arrows:
            ends.append(reduce_path(ends[-1], grade(args[i])))
        lifted = tuple(walk(arg, ends[slots[i]], on_var) for i, arg in enumerate(args))
        return ('coh', arity, ty, lifted)

    samples = []
    # Base each old variable at its original source, including the scalar.
    for t, ft in zip(variables, (f, g, k, h, a, s, b, p, q)):
        i, _ = outer_edge(infer(ctx, t))
        samples.append(((i + 1,), ft, t))
    # Folded terms with artificial joins, point identities and repeated labels.
    for sheet_id in range(1, 4):
        for left, mid, right in product((f, g, h), (a, s, b, p, q), (f, k, h)):
            middle = comp2(folded, 0, identity(folded, v(0)), mid)
            t = comp2(folded, 0, comp2(folded, 0, left, middle), right)
            samples.append(((sheet_id,), t, None))
            samples.append(((sheet_id,), identity(folded, t), None))

    blocks = {()}

    def collect(index, name):
        if index is not None:
            blocks.add(name)
        return v(0)

    for sheet, t, _ in samples:
        walk(t, sheet, collect)
    sheets = sorted({reduce_path(h, (i,)) for h in blocks for i in range(1, 4)})
    vertices = {sheet: v(i) for i, sheet in enumerate(sheets)}
    cover = [STAR] * len(sheets)
    retract = [v(sheet[0] - 1) for sheet in sheets]
    forget = [v(0) for _ in sheets]
    copies = {}
    for block in sorted(blocks):
        labels = [vertices[reduce_path(block, (i,))] for i in range(1, 4)]
        for i in range(3, len(ctx)):
            cover.append(subst_ty(ctx[i], labels))
            labels.append(v(len(cover) - 1))
            forget.append(fold[i])
            retract.append(v(i) if not block else
                           subst_tm(point_labels[i], (v(block[0] - 1),)))
        copies[block] = tuple(labels)
    cover, retract, forget = tuple(cover), tuple(retract), tuple(forget)
    check_ctx(cover)
    for i in range(len(cover)):
        assert infer(ctx, retract[i]) == subst_ty(cover[i], retract)
    counts = Counter()
    emitter = Emitter()

    def label(index, name):
        return vertices[name] if index is None else copies[name][index]

    for sheet, t, original in samples:
        lifted = walk(t, sheet, label)
        assert subst_tm(lifted, forget) == t
        ty = infer(cover, lifted)
        assert subst_ty(ty, forget) == infer(folded, t)
        answer = subst_tm(lifted, retract)
        assert infer(ctx, answer) == subst_ty(ty, retract)
        if original is not None:
            assert answer == original
        # Compute both immediate faces independently at the same initial
        # lift, except that an object target is at the terminal sheet.
        for i, face in enumerate(infer(folded, t)[2:]):
            anchor = reduce_path(sheet, grade(t)) if i and face == v(0) else sheet
            assert walk(face, anchor, label) == ty[2 + i]
        counts['folded terms lifted and retracted at their computed types'] += 1
    # A raw 3-cell whose folded labelling uses more than one translate.
    term = comp2(folded, 0, f, q)
    sheet = (1,)
    # This is a subexpression on this sheet of a sampled term up to its unit.
    lifted = walk(term, sheet, label)
    result = subst_tm(lifted, retract)
    emitter.check_type('foreign-attachment', ctx, result, subst_ty(infer(cover, lifted), retract))
    counts['distinct block copies needed'] = len(copies)
    counts['cover declarations in the checked retraction'] = len(cover)
    return counts, emitter


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    counts, emitter = check_lifts()
    if args.agda:
        module = emitter.module(args.agda.stem, 'Collapse of an attachment in another lifted block.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n',
                                            'open import CaTTExp.Gray.Pure\n'))
    for name, count in sorted(counts.items()):
        print(f'{count:,} {name}')
