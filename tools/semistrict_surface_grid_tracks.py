"""Check matching grid merges, their tracks, and a compound shared seam."""
from argparse import ArgumentParser
from functools import lru_cache
from itertools import product
from pathlib import Path

from catt import (arr, chain_tree, coh_between, comp2, disc_tree, glue_tree, infer,
                  src, tdim_tm, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_equal_rank import slots, suspend


def merge_tests():
    # Paths in a directed two-cycle, given by start and length. The lower
    # product on objects is XOR for either cut, so several seams fold together.
    paths = tuple(product(range(2), range(2)))
    factors = tuple(product(range(2), paths, paths))

    def end(a):
        return (a[0] + a[1]) % 2

    def pole(f, target):
        _, a, b = f
        return (end(a) ^ end(b)) if target else (a[0] ^ b[0])

    @lru_cache(None)
    def normal_forms(row):
        steps = []
        for i, (j, a, b) in enumerate(row):
            if a[1] == b[1] == 0:
                steps.append(row[:i] + row[i + 1:])
            if i + 1 == len(row):
                continue
            k, c, d = row[i + 1]
            if j == k and (end(a), end(b)) == (c[0], d[0]):
                factor = (j, (a[0], a[1] + c[1]), (b[0], b[1] + d[1]))
                steps.append(row[:i] + (factor,) + row[i + 2:])
        if not steps:
            return {row}
        return set.union(*(normal_forms(step) for step in steps))

    count = 0
    for a, b, c in product(factors, repeat=3):
        if pole(a, True) == pole(b, False) and pole(b, True) == pole(c, False):
            assert len(normal_forms((a, b, c))) == 1
            count += 1
    # The outside seam agrees but the two ordered component seams differ.
    a, b = (0, (0, 1), (0, 1)), (0, (0, 1), (0, 1))
    assert pole(a, True) == pole(b, False)
    assert normal_forms((a, b)) == {(a, b)}
    return count


def grid_tree(rank, cut, length):
    column = suspend(chain_tree(length), rank - cut - 2)
    return suspend((column, column), cut)


def temporal(ctx, a, b):
    return comp2(ctx, tdim_tm(ctx, a) - 1, a, b)


def row_track(ctx, rank, inputs, expressions):
    tree = suspend(chain_tree(len(inputs)), rank - 1)
    p = tree_ctx(tree)
    s, t = expressions(p, *slots(p))
    return coh_between(ctx, tree, inputs, s, t)


def associator(ctx, a, b, c):
    return row_track(ctx, tdim_tm(ctx, a), [a, b, c], lambda p, x, y, z: (
        temporal(p, temporal(p, x, y), z), temporal(p, x, temporal(p, y, z))))


def merge(ctx, rank, cut, a, b, c, d, reverse=False):
    tree = grid_tree(rank, cut, 2)
    p = tree_ctx(tree)
    x, y, z, w = slots(p)
    s = temporal(p, comp2(p, cut, x, z), comp2(p, cut, y, w))
    t = comp2(p, cut, temporal(p, x, y), temporal(p, z, w))
    return coh_between(ctx, tree, [a, b, c, d], *((t, s) if reverse else (s, t)))


def right_unit(ctx, a):
    rank = tdim_tm(ctx, a)
    tree = disc_tree(rank)
    p = tree_ctx(tree)
    x, = slots(p)
    return coh_between(ctx, tree, [a], temporal(p, x, identity(p, tgt(p, x))), x)


def check_tracks(rank, cut, emitter):
    top = rank - 1
    p = tree_ctx(grid_tree(rank, cut, 3))
    a, b, c, d, e, f = slots(p)
    x, y, z = comp2(p, cut, a, d), comp2(p, cut, b, e), comp2(p, cut, c, f)
    left = comp2(p, top, merge(p, rank, cut, a, b, d, e), z)
    left = temporal(p, left, merge(p, rank, cut, temporal(p, a, b), c, temporal(p, d, e), f))
    left = temporal(p, left, comp2(p, cut, associator(p, a, b, c), associator(p, d, e, f)))
    right = temporal(p, associator(p, x, y, z), comp2(p, top, x, merge(p, rank, cut, b, c, e, f)))
    right = temporal(p, right, merge(p, rank, cut, a, temporal(p, b, c), d, temporal(p, e, f)))

    def record(name, ctx, term, s, t):
        expected = arr(infer(ctx, s), s, t)
        assert infer(ctx, term) == expected
        if emitter:
            emitter.check_type(name, ctx, term, expected)

    record('threeMerges', p, head(p, left, right), left, right)
    record('threeMergesBack', p, head(p, right, left), right, left)

    p = tree_ctx(glue_tree(rank, cut, rank))
    a, b = slots(p)
    end_a, end_b = tgt(p, a), tgt(p, b)
    ia, ib = identity(p, end_a), identity(p, end_b)
    x = comp2(p, cut, a, b)
    left = temporal(p, merge(p, rank, cut, a, ia, b, ib), comp2(p, cut, right_unit(p, a), right_unit(p, b)))
    pair = glue_tree(top, cut, top)
    q = tree_ctx(pair)
    u, w = slots(q)
    paired_id = coh_between(p, pair, [end_a, end_b], comp2(q, cut, identity(q, u), identity(q, w)),
                            identity(q, comp2(q, cut, u, w)))
    right = temporal(p, comp2(p, top, x, paired_id), right_unit(p, x))
    record('identityMerge', p, head(p, left, right), left, right)

    # Two arbitrary tracks meet at a spatially pasted boundary. Carry the
    # contraction of a grid change and its reverse between them.
    p = tree_ctx(grid_tree(rank, cut, 2))
    theta = merge(p, rank, cut, *slots(p))
    reverse = merge(p, rank, cut, *slots(p), reverse=True)
    seam = src(p, theta)
    cancel = head(p, temporal(p, theta, reverse), identity(p, seam))
    track_type = arr(infer(p, seam), seam, seam)
    ctx = p + (track_type, track_type)
    a, b = v(len(p)), v(len(p) + 1)
    lifted = comp2(ctx, rank, comp2(ctx, rank, a, cancel), b)
    finish = comp2(ctx, rank, right_unit(ctx, a), b)
    start = temporal(ctx, temporal(ctx, a, temporal(ctx, theta, reverse)), b)
    record('compoundSeam', ctx, temporal(ctx, lifted, finish), start, temporal(ctx, a, b))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    print(f'{merge_tests()} folded three-factor rows have a unique reduced reading.')
    if args.agda_dir:
        args.agda_dir.mkdir(exist_ok=True, parents=True)
    for rank in (3, 4):
        for cut in range(rank - 1):
            emitter = Emitter() if args.agda_dir else None
            check_tracks(rank, cut, emitter)
            if emitter:
                name = f'GridTracks{rank}Cut{cut}'
                (args.agda_dir / (name + '.agda')).write_text(emitter.module(name, __doc__))
    print('Checked 20 raw judgments for triple overlap, identity overlap, and compound seam transport.')
