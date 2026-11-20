"""Check ordered replacement at composite faces and the endpoint contraction prism."""

from argparse import ArgumentParser
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, disc_tree, fv_tm, glue_tree, infer,
                  maximal_vars, src, sub_from, subst_tm, tgt, tree_ctx, v)
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_chart_paths import unitor
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity


def diagram():
    lower = (STAR,) * 5
    for i, j in ((0, 1), (1, 3), (0, 2), (2, 3), (3, 4)):
        lower += (arr(STAR, v(i), v(j)),)
    return lower, comp2(lower, 0, v(5), v(6)), comp2(lower, 0, v(7), v(8)), v(9)


def loop(arity, atom, wire, rank):
    cut = rank - 2
    base = comp2(arity, cut, atom, wire)
    front = comp2(arity, cut, unitor(arity, atom), wire)
    return comp2(arity, rank, front, head(arity, tgt(arity, front), base))


def check(rank, lower, a, b, wire, emitter):
    cut = rank - 2
    arity = tree_ctx(glue_tree(rank, cut, rank - 1))
    atom, tail = map(v, maximal_vars(arity))
    base = comp2(arity, cut, atom, tail)
    h = loop(arity, atom, tail, rank)

    def pair(target, x):
        return sub_from(arity, target, {atom[1]: x, tail[1]: wire})

    old = lower + (arr(infer(lower, a), a, b),)
    z = v(len(lower))
    x, y, left, middle, right = (v(len(lower) + i) for i in range(5))
    expanded = lower + (infer(lower, a), infer(lower, b))
    common = infer(lower, a)
    expanded += (arr(common, a, x), arr(common, x, y), arr(common, y, b))
    check_ctx(expanded)
    split = comp2(expanded, rank - 1, comp2(expanded, rank - 1, left, middle), right)
    collapse = tuple(map(v, range(len(lower)))) + (a, b, identity(old, a), z, identity(old, b))
    grown = tuple(map(v, range(len(lower)))) + (split,)
    hz = subst_tm(h, pair(old, z))
    hs = subst_tm(hz, grown)
    returned = subst_tm(hs, collapse)
    padded = subst_tm(split, collapse)
    assert src(expanded, split) == a and tgt(expanded, split) == b
    assert all(i[1] in fv_tm(hs) for i in (left, middle, right))
    assert returned == subst_tm(h, pair(old, padded)) and returned != hz

    disk = tree_ctx(disc_tree(rank))
    t = v(len(disk) - 1)
    padded_t = comp2(disk, rank - 1, comp2(disk, rank - 1, identity(disk, src(disk, t)), t),
                     identity(disk, tgt(disk, t)))
    eta = subst_tm(head(disk, t, padded_t), sub_from(disk, old, {t[1]: z}))
    moving = tree_ctx(glue_tree(rank + 1, cut, rank - 1))
    step, stationary = map(v, maximal_vars(moving))
    sub = sub_from(moving, old, {step[1]: eta, stationary[1]: wire})
    transfer = comp2(moving, cut, step, stationary)
    def moving_loop(face):
        return subst_tm(h, sub_from(arity, moving, {atom[1]: face, tail[1]: stationary}))
    path1 = comp2(moving, rank, moving_loop(src(moving, step)), transfer)
    path2 = comp2(moving, rank, transfer, moving_loop(tgt(moving, step)))
    square = subst_tm(head(moving, path1, path2), sub)
    actual = comp2(old, cut, eta, wire)
    expect_square = arr(infer(old, comp2(old, rank, hz, actual)),
                        comp2(old, rank, hz, actual), comp2(old, rank, actual, returned))
    assert infer(old, square) == expect_square
    emitter.check_typed(f'ordered-{rank}', old, square)
    emitter.check_type(f'ordered-{rank}', old, square, expect_square)

    # Keep the common poles fixed, send the positive face to the negative face,
    # and the generating arrow to the weak identity at that face.
    low = src(arity, atom)
    minus = sub_from(arity, arity, {atom[1]: identity(arity, low), tail[1]: tail})
    h0, u0 = (subst_tm(t, minus) for t in (h, base))
    transported = comp2(arity, rank - 1, u0, base)
    correction = head(arity, transported, base)
    low_path = comp2(arity, rank - 1, h0, base)
    start = comp2(arity, rank, low_path, correction)
    end = comp2(arity, rank, correction, h)
    prism = head(arity, start, end)

    bare = lower + (common, common, arr(common, x, y))
    check_ctx(bare)
    assignment = pair(bare, v(len(bare) - 1))
    real_h, real_h0, real_u, real_corr, witness = (
        subst_tm(t, assignment) for t in (h, h0, base, correction, prism))
    assert y[1] not in fv_tm(real_h0) and x[1] in fv_tm(real_h0)
    assert v(len(bare) - 1)[1] in fv_tm(real_h)
    l = comp2(bare, rank, comp2(bare, rank - 1, real_h0, real_u), real_corr)
    r = comp2(bare, rank, real_corr, real_h)
    expected = arr(infer(bare, l), l, r)
    assert infer(bare, witness) == expected
    emitter.check_typed(f'endpoint-{rank}', bare, witness)
    emitter.check_type(f'endpoint-{rank}', bare, witness, expected)


if __name__ == '__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('--agda', type=Path)
    args = cli.parse_args()
    lower, a, b, wire = diagram()
    emitter = Emitter()
    for rank in (2, 3, 4):
        check(rank, lower, a, b, wire, emitter)
        lower, a, b, wire = susp_ctx(lower), susp_tm(a), susp_tm(b), susp_tm(wire)
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Ordered replacement and endpoint contraction.'))
    print('3 replacements with composite faces and 3 endpoint prisms checked')
