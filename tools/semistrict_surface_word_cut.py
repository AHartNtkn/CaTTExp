"""Check the ordinary disc computations in the projection of binary surface words."""

from argparse import ArgumentParser
from collections import Counter
from pathlib import Path

from catt import STAR, comp2, disc_tree, glue_tree, infer, maximal_vars, tdim, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_cut import Cut
from semistrict_surface_scalar_cube import exchange


def disc_expression(ctx, term):
    """Return (variable, identity height) with a justification at every disc head."""
    if term[0] == 'v':
        return (term[1], 0)
    _, arity, ty, args = term
    height = max(tdim(a) + 1 for a in arity)
    assert arity == tree_ctx(disc_tree(height))
    top = len(arity) - 1
    rank = tdim(ty) + 1
    if rank == height:
        assert height >= 1
        _, _, source, target = arity[top]
        assert disc_expression(arity, ty[2]) == (source[1], 0)
        assert disc_expression(arity, ty[3]) == (target[1], 0)
        return disc_expression(ctx, args[top])
    assert rank > height
    x = disc_expression(arity, ty[2])
    assert x == disc_expression(arity, ty[3]) and x[0] == top
    var, n = disc_expression(ctx, args[top])
    return var, n + x[1] + 1


def check(counts, emitter):
    for p in range(1, 5):
        for q in range(1, 5):
            for k in range(min(p, q)):
                ctx = tree_ctx(glue_tree(p, k, q))
                a, b = map(v, maximal_vars(ctx))
                term = comp2(ctx, k, a, b)
                objects = [i for i, ty in enumerate(ctx) if ty == STAR]
                for column in range(len(objects) - 1):
                    cut = Cut(ctx, objects[column + 1:])
                    lower = cut.context()
                    projected = cut.term(term)
                    assert infer(lower, projected) == cut.type(infer(ctx, term))
                    if k == 0:
                        var, n = disc_expression(lower, projected)
                        height = (p, q)[column]
                        assert var == len(lower) - 1 and n == max(p, q) - height
                    else:
                        x, y = map(v, maximal_vars(lower))
                        assert projected == comp2(lower, k - 1, x, y)
                    counts['mixed and equal-rank binary cuts'] += 1

    square = tree_ctx(glue_tree(2, 0, 2))
    a, b = map(v, maximal_vars(square))
    j = exchange(square, a, b)
    objects = [i for i, ty in enumerate(square) if ty == STAR]
    for column in range(2):
        cut = Cut(square, objects[column + 1:])
        lower = cut.context()
        projected = cut.term(j)
        assert infer(lower, projected) == cut.type(infer(square, j))
        emitter.check_type('cut-square-' + str(column), lower, projected, cut.type(infer(square, j)))

        # Read the two actual restricted paths, including their raw unary
        # heads. Their disc computations give opposite unit placements.
        x, = map(v, maximal_vars(lower))
        for endpoint, name in zip(infer(square, j)[2:], ['late', 'early']):
            path = cut.term(endpoint)
            arity, args = path[1], path[3]
            assert arity == tree_ctx(glue_tree(1, 0, 1))
            pairs = [disc_expression(lower, args[i]) for i in maximal_vars(arity)]
            y = (x[1], 0)
            sx, tx = infer(lower, x)[2:]
            right_first = (name == 'late') == (column == 1)
            assert pairs == ([y, (tx[1], 1)] if right_first else [(sx[1], 1), y])
            counts['exchange faces with unit positions'] += 1


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    counts = Counter()
    emitter = Emitter()
    check(counts, emitter)
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Both projections of the Gray square.'))
    for label, count in sorted(counts.items()):
        print(f'{count:,} {label}')
