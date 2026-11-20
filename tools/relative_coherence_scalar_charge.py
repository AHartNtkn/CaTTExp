"""Detect one-way comparisons by a rational matrix evaluation of based routes."""
from argparse import ArgumentParser
from fractions import Fraction
from itertools import product
from pathlib import Path

from catt import arr, comp2, infer, ps_dim, src, tdim, tgt, tree_ctx
from emit_agda import Emitter
from partial_cylinder_steiner import trees
from relative_coherence_cut import top_counts
from relative_coherence_spherical_lift import witness


def sandwich(column):
    # A cap proportional to the transpose of the given cup makes V the identity.
    squared_norm = sum(y * y for y in column)
    cap = tuple(Fraction(x, squared_norm) for x in column)
    swapped = (column[0], column[2], column[1], column[3])
    return tuple(sum(x * y for x, y in zip(cap, route)) for route in (column, swapped))


def arity_checks(max_edges):
    arities = labellings = 0
    for size in range(4, max_edges + 1):
        for tree in trees(size):
            ctx = tree_ctx(tree)
            if ps_dim(ctx) != 4:
                continue
            edges = [(t[2][1], t[3][1]) for t in ctx if tdim(t) + 1 == 4]
            sources = {s for s, _ in edges}
            targets = {t for _, t in edges}
            assert len(sources) == len(targets) == len(edges)
            for weights in product((0, 1), repeat=len(edges)):
                potentials = {s: 0 for s in sources - targets}
                for (s, t), w in zip(edges, weights):
                    assert s in potentials and t not in potentials
                    potentials[t] = potentials[s] + w
                assert sum(potentials[t] for t in targets - sources) == sum(weights)
                labellings += 1
            arities += 1
    print(f"{arities} rank-four arities and {labellings} binary weight labellings.")


def typed_family(ctx, alpha, beta, limit, agda):
    even, odd = src(ctx, beta), tgt(ctx, alpha)
    common = infer(ctx, even)
    assert infer(ctx, odd) == common and tgt(ctx, beta) == src(ctx, alpha)
    bridge = comp2(ctx, 3, beta, alpha)
    emitter = Emitter()
    def flank(term):
        return comp2(ctx, 2, comp2(ctx, 2, odd, term), even)

    f, u, v = bridge, even, odd
    for n in range(1, limit + 1):
        assert infer(ctx, f) == arr(common, u, v)
        assert top_counts(ctx, f) == {alpha[1]: n, beta[1]: n}
        if n <= 2:
            emitter.check_typed(f"forward{n}", ctx, f)
            emitter.check_type(f"poles{n}", ctx, f, arr(common, u, v))
        # Include an odd inactive term on the left and an even one on the right.
        framed = flank(f)
        expected = arr(common, flank(u), flank(v))
        assert infer(ctx, framed) == expected
        assert top_counts(ctx, framed) == top_counts(ctx, f)
        if n == 1:
            emitter.check_typed("flanked", ctx, framed)
            emitter.check_type("flankedPoles", ctx, framed, expected)
        if n < limit:
            f = comp2(ctx, 2, f, bridge)
            u, v = comp2(ctx, 2, u, even), comp2(ctx, 2, v, odd)
    if agda:
        agda.write_text(emitter.module(agda.stem, "Directed comparisons of based routes."))
    print(f"Checked the endpoints and two generator counts for powers 1 through {limit}, bare and flanked.")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path)
    args = parser.parse_args()
    samples = [sandwich(column) for column in product((1, 2), repeat=4)]
    assert all(direct == 1 for direct, _ in samples)
    assert sum(around != 1 for _, around in samples) == 8
    assert sandwich((1, 1, 2, 1)) == (1, Fraction(6, 7))
    print("16 rational matrix evaluations; 8 detect the exchange; chosen U/V = 6/7.")
    arity_checks(9)
    ctx, alpha, beta = witness(None)
    typed_family(ctx, alpha, beta, 4, args.agda)


if __name__ == "__main__":
    main()
