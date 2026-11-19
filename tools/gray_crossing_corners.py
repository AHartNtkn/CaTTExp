"""Type-check the four corner substitutions on I ⊗ D^b inside D³ ⊗ D^(b+2)."""
import argparse
from itertools import product
from pathlib import Path

from canonical_gray_two_discs import strict_interpreter
from catt import (STAR, arr, check_ctx, comp2, disc_tree, infer, maximal_vars,
                  sub_from, subst_tm, subst_ty, tree_ctx, v)
from ct_suspension import L, R, build, susp_ty
from emit_agda import Emitter
from gray_crossing_paths import coordinates, square_image
from gray_globe_comparison import atom, face, globe
from gray_polygon_panels import faces, generic_filler


def ambient(b):
    """The pure globes and the four mixed squares needed at the corners."""
    context = []
    labels = {}

    def declare(g, ty):
        labels[g] = v(len(context))
        context.append(ty)

    for g in sorted(product(globe(3), globe(b+2)), key=lambda g: g[0][0]+g[1][0]):
        if g[0][0] and g[1][0]:
            continue
        if g[0][0]+g[1][0]:
            s, t = (labels[face(atom(g), i)[-1][0][0]] for i in (0, 1))
            ty = arr(infer(tuple(context), s), s, t)
        else:
            ty = STAR
        declare(g, ty)

    for s, t in product(range(2), repeat=2):
        pa, qb = (1, s), (1, t)
        src = comp2(tuple(context), 0, labels[(0, 0), qb], labels[pa, (0, 1)])
        tgt = comp2(tuple(context), 0, labels[pa, (0, 0)], labels[(0, 1), qb])
        declare((pa, qb), arr(infer(tuple(context), src), src, tgt))
    check_ctx(tuple(context))
    return tuple(context), labels


def steps(i, j):
    before = (['A'] if i else []) + ([] if j else ['B'])
    after = ([] if i else ['A']) + (['B'] if j else [])
    return before + ['square'] + after


def path_face(context, term, rank, side):
    for _ in range(rank - 1):
        term = infer(context, term)[2 + side]
    return term


def actual_strip(context, labels, b, i, j, order):
    sa = sb = 0
    values = []
    for step in order:
        if step == 'A':
            pure = labels[(3, 2), (0, i)]
            value = (L(context, 3, labels[(0, 0), (1, sb)], pure) if i else
                     R(context, 3, pure, labels[(0, 1), (1, sb)]))
            sa = 1
        elif step == 'B':
            pure = labels[(0, j), (b+2, 2)]
            value = (L(context, b+2, labels[(1, sa), (0, 0)], pure) if j else
                     R(context, b+2, pure, labels[(1, sa), (0, 1)]))
            sb = 1
        else:
            assert (sa, sb) == (i, 1-j)
            value = labels[(1, sa), (1, sb)]
        values.append(value)
    return values


def check(level, context, labels, i, j, emitter):
    b = level.k
    order = steps(i, j)
    dims = {'A': 3, 'B': b+2, 'square': 2}
    strip = tree_ctx((tuple(disc_tree(dims[s]-2) for s in order),))
    maxima = dict(zip(order, maximal_vars(strip)))
    actual = actual_strip(context, labels, b, i, j, order)
    substitution = sub_from(strip, context, dict(zip(maximal_vars(strip), actual)))
    s1 = path_face(strip, v(maxima[order[0]]), dims[order[0]], 0)
    t1 = path_face(strip, v(maxima[order[-1]]), dims[order[-1]], 1)
    rho = [v(0), v(1), s1, t1]
    pfaces = faces(strip, v(maxima['A']), 1)
    qfaces = faces(strip, v(maxima['B']), b)
    source = {index: (('g', 0, '-+'[side]), q) for (side, q), index in level.end.items()}
    source.update((index, (('g', 1, '*'), q)) for q, index in level.mix.items())
    evaluate = strict_interpreter(context, tuple(labels))
    for index, ty in enumerate(level.G):
        p, q = source[index]
        wanted = subst_ty(susp_ty(susp_ty(ty)), rho)
        term = generic_filler(strip, wanted, (pfaces[p], v(maxima['square']), qfaces[q]))
        image = subst_tm(term, substitution)
        expected = subst_ty(wanted, substitution)
        assert infer(context, image) == expected
        p_gen, q_gen = ((g[1], '-+*'.index(g[2])) for g in (p, q))
        assert coordinates(evaluate(image)) == square_image(atom((p_gen, (0, i), (0, j), q_gen)))
        if emitter is not None and p[2] == q[2] == '*':
            emitter.check_type(f'corner-{i}-{j}-rank-{b}', context, image, expected)
        rho.append(term)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('degree', type=int, help='largest b, at least one')
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.degree < 1:
        parser.error('degree must be positive')
    emitter = Emitter() if args.agda else None
    for level in build(args.degree)[1:]:
        context, labels = ambient(level.k)
        for i, j in product(range(2), repeat=2):
            check(level, context, labels, i, j, emitter)
        print(f'Checked all four corner substitutions through global degree {level.k+3}')
    if emitter is not None:
        args.agda.write_text(emitter.module(args.agda.stem, 'From tools/gray_crossing_corners.py.'))
