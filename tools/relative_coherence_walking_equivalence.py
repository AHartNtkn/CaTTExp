"""Compare both inverse choices in the source attachment for a walking equivalence."""
from argparse import ArgumentParser
from functools import reduce
from pathlib import Path

from catt import (STAR, arr, chain_tree, check_ctx, coh_between, comp2, disc_tree,
                  infer, maximal_vars, sub_from, subst_tm, tree_ctx, v)
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity


def walking_piece():
    points = (STAR, STAR)
    z, g = v(0), v(1)
    ctx = points + (arr(STAR, z, g), arr(STAR, g, z), arr(STAR, g, z))
    a, b, c = v(2), v(3), v(4)
    iz, ig = identity(ctx, z), identity(ctx, g)
    ab, ca = comp2(ctx, 0, a, b), comp2(ctx, 0, c, a)
    def declare(s, t):
        nonlocal ctx
        ty = arr(infer(ctx, s), s, t)
        variable = v(len(ctx))
        ctx += (ty,)
        return variable
    right, left = declare(ab, iz), declare(ca, ig)
    right_back, left_back = declare(iz, ab), declare(ig, ca)
    check_ctx(ctx)
    disk = tree_ctx(disc_tree(1))
    x = v(2)
    def unit(term, at_left, insert):
        long = (comp2(disk, 0, identity(disk, v(0)), x) if at_left
                else comp2(disk, 0, x, identity(disk, v(1))))
        start, end = (x, long) if insert else (long, x)
        return coh_between(ctx, disc_tree(1), [term], start, end)
    triple = tree_ctx(chain_tree(3))
    x1, x2, x3 = map(v, maximal_vars(triple))
    l = comp2(triple, 0, comp2(triple, 0, x1, x2), x3)
    r = comp2(triple, 0, x1, comp2(triple, 0, x2, x3))
    labels = sub_from(triple, ctx, dict(zip(maximal_vars(triple), (c, a, b))))
    def vertical(parts):
        return reduce(lambda s, t: comp2(ctx, 1, s, t), parts)
    bc = vertical((unit(b, True, True), comp2(ctx, 0, left_back, b),
                   subst_tm(head(triple, l, r), labels), comp2(ctx, 0, c, right),
                   unit(c, False, False)))
    cb = vertical((unit(c, False, True), comp2(ctx, 0, c, right_back),
                   subst_tm(head(triple, r, l), labels), comp2(ctx, 0, left, b),
                   unit(b, True, False)))
    ac = comp2(ctx, 0, a, c)
    missing = vertical((comp2(ctx, 0, a, cb), right))
    missing_back = vertical((right_back, comp2(ctx, 0, a, bc)))
    ia = comp2(ctx, 0, iz, a)
    return ctx, [('bc', bc, b, c), ('cb', cb, c, b), ('cancel', missing, ac, iz),
                 ('expand', missing_back, iz, ac), ('onA', unit(a, True, False), ia, a),
                 ('offA', unit(a, True, True), a, ia), ('onB', right_back, iz, ab),
                 ('offB', right, ab, iz)]


def check(file):
    ctx, checks = walking_piece()
    emitter = Emitter()
    for k in range(5):
        check_ctx(ctx)
        for name, t, s, u in checks:
            ty = arr(infer(ctx, s), s, u)
            assert infer(ctx, t) == ty
            if file:
                emitter.check_type(name + str(k), ctx, t, ty)
        if k < 4:
            ctx = susp_ctx(ctx)
            checks = [(name, susp_tm(t), susp_tm(s), susp_tm(u)) for name, t, s, u in checks]
    if file:
        file.write_text(emitter.module(file.stem, 'Missing cancellations for independent inverse data.'))
    print('Both inverse comparisons and all three mixed labels in both directions, at suspension levels 0 through 4.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    check(parser.parse_args().agda)
