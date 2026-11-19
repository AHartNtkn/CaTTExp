"""Check a four-dimensional comparison on two cube variables and the degree-five top cells."""
import argparse
from itertools import combinations
from pathlib import Path

from canonical_gray_cube import build_cube
from canonical_gray_two_discs import cube_generators, strict_interpreter
from catt import (STAR, arr, check_ctx, comp2, disc_tree, infer, maximal_vars, src,
                  sub_from, subst_tm, subst_ty, tgt, tree_ctx, v)
from emit_agda import Emitter
from gray_globe_comparison import atom, strict_cells


def wedge_of_cubes():
    cube, _ = build_cube()
    basis = tuple(cube_generators())
    context = list(cube)
    right = [v(7)]  # initial corner of the second cube is the final corner of the first
    labels = [g + ((0, 0),) * 3 for g in basis]
    for g, ty in zip(basis[1:], cube[1:]):
        transported = subst_ty(ty, right)
        right.append(v(len(context)))
        context.append(transported)
        labels.append(((0, 1),) * 3 + g)
    return tuple(context), labels, v(len(cube) - 1), right[-1]


def ordered_comp(context, left, right, left_first):
    def edge(term, side):
        while infer(context, term)[1] != STAR:
            term = infer(context, term)[2 + side]
        return term

    if left_first:
        a = comp2(context, 0, left, edge(right, 0))
        b = comp2(context, 0, edge(left, 1), right)
    else:
        a = comp2(context, 0, edge(left, 0), right)
        b = comp2(context, 0, left, edge(right, 1))
    return comp2(context, 1, a, b)


def two_cube_comparison(emitter):
    pair = tree_ctx(disc_tree(2) + disc_tree(2))
    arguments = tuple(map(v, maximal_vars(pair)))
    left, right = (ordered_comp(pair, *arguments, order) for order in (True, False))
    swap = ('coh', pair, arr(infer(pair, left), left, right), tuple(map(v, range(len(pair)))))
    infer(pair, swap)

    generic = tree_ctx(disc_tree(3) + disc_tree(3))
    a, b = map(v, maximal_vars(generic))

    def interchange(side):
        ends = [side(generic, t) for t in (a, b)]
        return subst_tm(swap, sub_from(pair, generic, dict(zip(maximal_vars(pair), ends))))

    first = comp2(generic, 2, ordered_comp(generic, a, b, True), interchange(tgt))
    second = comp2(generic, 2, interchange(src), ordered_comp(generic, a, b, False))
    boundary = arr(infer(generic, first), first, second)
    comparison = ('coh', generic, boundary, tuple(map(v, range(len(generic)))))
    assert infer(generic, comparison) == boundary

    context, labels, left_cube, right_cube = wedge_of_cubes()
    check_ctx(context)
    sub = sub_from(generic, context, dict(zip(maximal_vars(generic), (left_cube, right_cube))))
    term, wanted = subst_tm(comparison, sub), subst_ty(boundary, sub)
    assert infer(context, term) == wanted and wanted[2] != wanted[3]
    evaluate = strict_interpreter(context, labels)
    a_value, b_value = map(evaluate, wanted[2:])
    assert a_value == b_value
    assert a_value[-1][0] == tuple(sorted((labels[left_cube[1]], labels[right_cube[1]])))
    assert evaluate(term) == a_value + (((), ()),)
    if emitter:
        emitter.check_type('two-cubes-exchange', context, term, wanted)
    print('Two cube variables: distinct parallel 3-terms, both active cubes, identity-image 4-filler')


def five_dimensional_products():
    for count in range(1, 6):
        for cuts in combinations(range(1, 5), count - 1):
            endpoints = (0,) + cuts + (5,)
            shape = tuple(b - a for a, b in zip(endpoints, endpoints[1:]))
            level = strict_cells(shape, 5)
            top_cells = [x for x in level if x[-1][0]]
            assert top_cells == [atom(tuple((rank, 2) for rank in shape))]
            print(f'{shape}: one nonidentity among {len(level)} strict 5-cells')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    two_cube_comparison(emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Four-dimensional cube comparison.'))
    five_dimensional_products()
