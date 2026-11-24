"""Test column factorization and literal Godement boundaries in the joined theory."""
import argparse
from functools import reduce
from itertools import product
from pathlib import Path

from catt import comp2, infer, maximal_vars, tree_ctx, ucomp, v
from ct_suspension import ident
from semistrict_surface_full_binary import evaluate, generators
from semistrict_surface_insertion_cut import Assertions


def fold(ctx, cut, row):
    return reduce(lambda left, right: comp2(ctx, cut, left, right), row)


def rows(ctx, counts):
    peaks = iter(map(v, maximal_vars(ctx)))
    return [[next(peaks) for _ in range(max(1, n))] for n in counts]


def main(checkout):
    checks = Assertions()
    for width in range(1, 5):
        for counts in product(range(4), repeat=width):
            if not any(counts):
                continue
            ctx = tree_ctx(tuple(((),) * n for n in counts))
            columns = [fold(ctx, 1, row) if n else ident(ctx, row[0])
                       for n, row in zip(counts, rows(ctx, counts))]
            checks.equal(ctx, ucomp(ctx), fold(ctx, 0, columns), 'standard 2-head factorizations')
    ctx = tree_ctx((((), ()), ((), ())))
    (a, c), (b, d) = rows(ctx, (2, 2))
    horizontal = comp2(ctx, 0, comp2(ctx, 1, a, c), comp2(ctx, 1, b, d))
    vertical = comp2(ctx, 1, comp2(ctx, 0, a, b), comp2(ctx, 0, c, d))
    assert infer(ctx, horizontal) == infer(ctx, vertical)
    assert evaluate(horizontal, generators(ctx)) == evaluate(vertical, generators(ctx))
    checks.run(checkout / 'target/release/catt_strict')
    print('Generic Godement grid has literally parallel faces and identical full binary normals')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path)
    main(parser.parse_args().checkout.resolve())
