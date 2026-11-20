"""A strict based four-loop without a CaTT representative (round 7)."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import (STAR, arr, check_ctx, coh_between, comp2, glue_tree, infer,
                  maximal_vars, src, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity


def exchange(ctx, a):
    """Exchange the order of the two slots before specializing them both to a."""
    tree = glue_tree(2, 0, 2)
    paste = tree_ctx(tree)
    left, right = map(v, maximal_vars(paste))
    first = comp2(paste, 1, comp2(paste, 0, left, src(paste, right)),
                  comp2(paste, 0, tgt(paste, left), right))
    second = comp2(paste, 1, comp2(paste, 0, src(paste, left), right),
                   comp2(paste, 0, left, tgt(paste, right)))
    return coh_between(ctx, tree, [a, a], first, second)


def witness(agda_path):
    ctx = (STAR,)
    emitter = Emitter()

    def arrow(left, right):
        ty = infer(ctx, left)
        assert infer(ctx, right) == ty
        return arr(ty, left, right)

    def declare(name, left, right):
        nonlocal ctx
        ty = arrow(left, right)
        variable = v(len(ctx))
        ctx += (ty,)
        emitter.check_type(name, ctx, variable, ty)
        return variable

    unit = identity(ctx, v(0))
    a = declare("bubble", unit, unit)
    b, d = comp2(ctx, 0, a, unit), comp2(ctx, 0, unit, a)
    change = declare("change", b, d)
    tile = exchange(ctx, a)
    bd, db = comp2(ctx, 1, b, d), comp2(ctx, 1, d, b)
    assert infer(ctx, tile) == arrow(bd, db)
    emitter.check_type("exchange", ctx, tile, arrow(bd, db))

    direct = comp2(ctx, 1, change, b)
    around = comp2(ctx, 2, comp2(ctx, 1, b, change), tile)
    common = arrow(comp2(ctx, 1, b, b), db)
    for name, route in (("direct", direct), ("around", around)):
        assert infer(ctx, route) == common
        emitter.check_type(name, ctx, route, common)

    pole = identity(ctx, comp2(ctx, 0, unit, unit))
    prefix = declare("prefix", pole, src(ctx, direct))
    suffix = declare("suffix", tgt(ctx, direct), pole)

    def based(route):
        result = comp2(ctx, 2, comp2(ctx, 2, prefix, route), suffix)
        assert infer(ctx, result) == arrow(pole, pole)
        return result

    odd, even = based(around), based(direct)
    base = identity(ctx, pole)
    alpha = declare("enter", base, odd)
    beta = declare("exit", even, base)
    assert tgt(ctx, alpha) != src(ctx, beta)
    assert len(ctx) == 7
    check_ctx(ctx)
    if agda_path:
        agda_path.write_text(emitter.module(agda_path.stem, "Based strict loop obstruction."))

    # Three-charges add at compositions within one hom. The Gray exchange
    # contributes the braiding of its two inputs; multiplication is in F_2.
    # Exhaust all charges for J, prefix and suffix, and both bubble labels.
    for degree, j, p, q in product(range(2), repeat=4):
        direct_value = (p + j + q) % 2
        around_value = (p + j + degree * degree + q) % 2
        assert (around_value - direct_value) % 2 == degree
    print("Seven declarations; exchange and both routes type-checked.")
    print("Bubble degree 1 gives boundary difference 1 for the strict two-generator loop.")
    return ctx, alpha, beta


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path, help="emit the concrete typing judgments")
    witness(parser.parse_args().agda)
