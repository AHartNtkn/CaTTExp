"""Construct raw total terms by directed unary prisms and ordered composition."""
from argparse import ArgumentParser
from functools import cache
from pathlib import Path

from catt import (comp2, disc_tree, glue_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, tdim_tm, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_interval_generator import trees


def pole(ctx, term, degree, side):
    while tdim_tm(ctx, term) > degree:
        term = (src, tgt)[side](ctx, term)
    return term


def ordered(ctx, cut, a, b):
    """Godement's right-first spelling; only call heads with a fixed whisker."""
    if min(tdim_tm(ctx, a), tdim_tm(ctx, b)) == cut + 1:
        return comp2(ctx, cut, a, b)
    first = comp2(ctx, cut, pole(ctx, a, cut + 1, 0), b)
    last = comp2(ctx, cut, a, pole(ctx, b, cut + 1, 1))
    return ordered(ctx, cut + 1, first, last)


def prism_at(ctx, a, b, moving_left):
    moving = a if moving_left else b
    arity, term = unary(tdim_tm(ctx, moving) - 1, moving_left)
    labels = dict(zip(maximal_vars(arity), (a, b), strict=True))
    return subst_tm(term, sub_from(arity, ctx, labels))


@cache
def unary(rank, moving_left):
    """The two signed hemisphere pastes on a globe and an adjacent edge."""
    dims = (rank + 1, 2) if moving_left else (2, rank + 1)
    ctx = tree_ctx(glue_tree(dims[0], 0, dims[1]))
    first, second = map(v, maximal_vars(ctx))
    x, edge = (first, second) if moving_left else (second, first)

    def beside(y, z):
        return comp2(ctx, 0, y, z) if moving_left else comp2(ctx, 0, z, y)

    def mixed(degree, side):
        y = pole(ctx, x, degree + 1, side)
        if degree == 0:
            return beside(y, edge)
        a, b = (y, edge) if moving_left else (edge, y)
        return prism_at(ctx, a, b, moving_left)

    lower = comp2(ctx, 1, mixed(0, 0), beside(x, tgt(ctx, edge)))
    upper = comp2(ctx, 1, beside(x, src(ctx, edge)), mixed(0, 1))
    if not moving_left:
        lower, upper = upper, lower
    for cut in range(1, rank):
        before, after = mixed(cut, 0), mixed(cut, 1)
        if moving_left:
            lower, upper = comp2(ctx, cut + 1, before, upper), comp2(ctx, cut + 1, lower, after)
        else:
            lower, upper = comp2(ctx, cut + 1, lower, after), comp2(ctx, cut + 1, before, upper)
    assert infer(ctx, lower) == infer(ctx, upper)
    return ctx, head(ctx, lower, upper)


def total(tree):
    """Compute column terms in the ambient context, then grow the chosen interval."""
    ctx = tree_ctx(tree)
    next_variable = 1

    def columns(branches, depth):
        nonlocal next_variable
        values = []
        for branch in branches:
            arrow = v(next_variable + 1)
            next_variable += 2
            children = columns(branch, depth + 1)
            if children:
                arrow = children[0]
                for child in children[1:]:
                    arrow = ordered(ctx, depth + 1, arrow, child)
            values.append(arrow)
        return values

    spans = columns(tree, 0)
    if not spans:
        return ctx, v(0)
    degrees = [tdim_tm(ctx, span) for span in spans]
    if sum(d > 2 for d in degrees) > 1:
        raise ValueError("two columns contain generating 3-cells")
    pivot = degrees.index(max(degrees))
    result = spans[pivot]
    neighbors = [(False, span) for span in reversed(spans[:pivot])]
    neighbors.extend((True, span) for span in spans[pivot + 1:])
    for moving_left, span in neighbors:
        a, b = (result, span) if moving_left else (span, result)
        if tdim_tm(ctx, span) == 1:
            result = comp2(ctx, 0, a, b)
        else:
            result = prism_at(ctx, a, b, moving_left)
    assert next_variable == len(ctx)
    assert tdim_tm(ctx, result) == 1 + sum(d - 1 for d in degrees)
    return ctx, result


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    count = 0
    for size in range(6):
        for tree in trees(size):
            if sum(any(child for child in column) for column in tree) <= 1:
                total(tree)
                count += 1
    emitter = Emitter()
    edge, tall = disc_tree(1), disc_tree(2)
    cases = {'square': (edge, edge), 'fourCube': (edge,) * 4,
             'leftPrism': (disc_tree(3), edge), 'rightPrism': (edge, disc_tree(3)),
             'interior': (edge, tall, edge), 'subdivided': (((), ()), ((), ((),))),
             'vertex': (edge, (), edge)}
    for name, tree in cases.items():
        ctx, term = total(tree)
        emitter.check_typed(name, ctx, term)
        a = emitter.ty(infer(ctx, term))
        t = emitter.tm(term)
        emitter.checks.append(f'{name}Full : cohCase {emitter.ctx(ctx)} {a} {t} {t} ≡ true\n'
                              f'{name}Full = refl\n')
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('DirectedFullArities', __doc__)
        (args.agda_dir / 'DirectedFullArities.agda').write_text(
            module.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))
    print(f'Constructed terms on {count} small trees and {len(cases)} named arities.')


if __name__ == '__main__':
    main()
