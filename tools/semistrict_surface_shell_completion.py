"""Verify the finite inverse presentations for one stationary puncture."""
from argparse import ArgumentParser
from collections import Counter
from pathlib import Path

from catt import arr, comp2, disc_tree, infer, src, tgt, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter


def round_trip_schema(rank, writer):
    """Check a step over a generic globe, where the two ends are distinct."""
    ctx = tree_ctx(disc_tree(rank))
    f = v(len(ctx) - 1)
    common, a, b = infer(ctx, f)[1:]
    reverse = arr(common, b, a)
    left, right = v(len(ctx)), v(len(ctx) + 1)
    ctx += (reverse, reverse)
    for first, second in ((f, right), (left, f)):
        composite = comp2(ctx, rank - 1, first, second)
        unit = ident(ctx, src(ctx, first))
        assert infer(ctx, composite) == infer(ctx, unit)
        assert src(ctx, composite) == tgt(ctx, composite) == src(ctx, first)
        common = infer(ctx, unit)
        ctx += (arr(common, composite, unit), arr(common, unit, composite))
    if writer is not None:
        name = writer.ctx(ctx)
        writer.checks.append(f'globe{rank} : {name} ⊢ctx\n'
                             f'globe{rank} = from-just (checkCtx {name})\n')


def completion(d, top):
    """Build integral cellular boundaries and the free-face attachment order."""
    degrees, boundary = [], []
    def attach(degree, chain):
        assert all(degrees[cell] == degree - 1 for cell in chain)
        square = Counter()
        for face, coefficient in chain.items():
            for cell, value in boundary[face].items():
                square[cell] += coefficient * value
        assert not any(square.values())
        degrees.append(degree)
        boundary.append(chain)
        return len(degrees) - 1

    sphere = attach(d, {})
    layer = [sphere]
    expansions = []
    for rank in range(d, top + 1):
        fits = []
        for f in layer:
            for _ in ('right', 'left'):
                inverse = attach(rank, {a: -v for a, v in boundary[f].items()})
                fit = attach(rank + 1, {f: -1, inverse: -1})
                fits.append(fit)
                expansions.append((inverse, fit))
        layer = fits
    mates = []
    for fit in layer:
        mate = attach(top + 1, {a: -v for a, v in boundary[fit].items()})
        mates.append(mate)

    # Change basis from each mate to its sum with the original disk.
    # Collapse elementary pairs in reverse attachment order. Each recorded
    # inverse must actually be a unit pivot and free of other cofaces.
    for mate, fit in zip(mates, layer, strict=True):
        assert boundary[mate].keys() == boundary[fit].keys()
        assert all(boundary[mate][c] + boundary[fit][c] == 0 for c in boundary[mate])
        boundary[mate] = {}
    live = set(range(len(degrees)))
    for inverse, fit in reversed(expansions):
        assert [cell for cell in live if inverse in boundary[cell]] == [fit]
        assert abs(boundary[fit][inverse]) == 1
        live.difference_update((inverse, fit))
    assert live == {sphere, *mates}
    assert all(not boundary[cell] for cell in live)
    return 2 + len(degrees), len(mates)  # point and stationary colour


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    writer = Emitter() if args.agda_dir else None
    for rank in range(4, 11):
        round_trip_schema(rank, writer)
    for n, expected in ((2, (319, 64)), (3, (639, 128))):
        size, spheres = completion(4 - n, 7)
        assert (size, spheres) == expected
        print(f'Rank {n}: {size} declarations, S^{4-n} and {spheres} local 8-spheres.')
    if writer is not None:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        (args.agda_dir / 'ShellCompletion.agda').write_text(
            writer.module('ShellCompletion', 'Generic based inverse and round-trip attachments.'))


if __name__ == '__main__':
    main()
