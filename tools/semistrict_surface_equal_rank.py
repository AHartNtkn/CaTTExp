"""Check the finite equal-rank presentation for the ordinary binary surface."""
from argparse import ArgumentParser
from functools import lru_cache
from itertools import product
from pathlib import Path

from catt import (arr, chain_tree, comp2, disc_tree, glue_tree, infer, maximal_vars, src,
                  tdim_tm, tgt, tree_ctx, ucomp, v)
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity


def suspend(tree, count):
    for _ in range(count):
        tree = (tree,)
    return tree


def grid(rank, cut):
    column = suspend(chain_tree(2), rank - cut - 2)
    return suspend((column, column), cut)


def slots(ctx):
    return [v(i) for i in maximal_vars(ctx)]


def pad(ctx, term, rank):
    for _ in range(tdim_tm(ctx, term), rank):
        term = identity(ctx, term)
    return term


@lru_cache(None)
def translate_word(ctx, term):
    if term[0] == 'v':
        return term
    _, arity, ty, labels = term
    args = [translate_word(ctx, labels[i]) for i in maximal_vars(arity)]
    if len(args) == 1:
        assert ty[2] == ty[3] == v(maximal_vars(arity)[0])
        return identity(ctx, args[0])
    assert len(args) == 2 and ty == ucomp(arity)[2]
    p, q = (tdim_tm(ctx, t) for t in args)
    cut, = [j for j in range(min(p, q)) if tree_ctx(glue_tree(p, j, q)) == arity]
    return comp2(ctx, cut, *(pad(ctx, t, max(p, q)) for t in args))


def equations(rank):
    top = rank - 1
    triple = tree_ctx(suspend(chain_tree(3), top))
    a, b, c = slots(triple)
    yield ('assoc', triple, comp2(triple, top, comp2(triple, top, a, b), c),
           comp2(triple, top, a, comp2(triple, top, b, c)))
    disc = tree_ctx(disc_tree(rank))
    a, = slots(disc)
    yield 'leftUnit', disc, comp2(disc, top, identity(disc, src(disc, a)), a), a
    yield 'rightUnit', disc, comp2(disc, top, a, identity(disc, tgt(disc, a))), a
    for cut in range(top):
        ctx = tree_ctx(grid(rank, cut))
        a, b, c, d = slots(ctx)
        yield (f'grid{cut}', ctx, comp2(ctx, cut, comp2(ctx, top, a, b), comp2(ctx, top, c, d)),
               comp2(ctx, top, comp2(ctx, cut, a, c), comp2(ctx, cut, b, d)))
        ctx = tree_ctx(glue_tree(top, cut, top))
        x, y = slots(ctx)
        yield (f'pairedIds{cut}', ctx, comp2(ctx, cut, identity(ctx, x), identity(ctx, y)),
               identity(ctx, comp2(ctx, cut, x, y)))


def reading(ctx, term, assignment):
    rank = tdim_tm(ctx, term)
    assert rank <= 2
    if rank < 2:
        return 0
    if term[0] == 'v':
        return assignment[term[1]]
    _, arity, ty, labels = term
    if len(maximal_vars(arity)) != 2 or ucomp(arity)[2] != ty:
        return 0
    a, b = [labels[i] for i in maximal_vars(arity)]
    twist = (tdim_tm(ctx, a), tdim_tm(ctx, b)) == (2, 1)
    return (reading(ctx, a, assignment) + reading(ctx, b, assignment) + twist) % 2


def check_rank(rank, directory):
    emitter = Emitter() if directory else None
    count = 0
    for name, ctx, a, b in equations(rank):
        ty = infer(ctx, a)
        assert ty == infer(ctx, b)
        assert (translate_word(ctx, a), translate_word(ctx, b)) == (a, b)
        if rank <= 2:
            moving = [i for i in maximal_vars(ctx) if tdim_tm(ctx, v(i)) == 2]
            for values in product(range(2), repeat=len(moving)):
                assignment = dict(zip(moving, values))
                assert reading(ctx, a, assignment) == reading(ctx, b, assignment)
        if emitter:
            emitter.check_type(name + 'Left', ctx, a, ty)
            emitter.check_type(name + 'Right', ctx, b, ty)
        count += 1
    mixed = 0
    for s in range(1, rank):
        for p, q in ((rank, s), (s, rank)):
            for j in range(s):
                ctx = tree_ctx(glue_tree(p, j, q))
                a, b = slots(ctx)
                word = comp2(ctx, j, a, b)
                replacement = translate_word(ctx, word)
                lo, hi = (translate_word(ctx, f(ctx, word)) for f in (src, tgt))
                ty = arr(infer(ctx, lo), lo, hi)
                assert infer(ctx, replacement) == ty
                if emitter:
                    emitter.check_type(f'padded{p}c{j}p{q}', ctx, replacement, ty)
                mixed += 1
    if emitter:
        name = f'EqualRank{rank}'
        (directory / (name + '.agda')).write_text(emitter.module(name, __doc__))
    return count, mixed


def compare_readings():
    line = tree_ctx(chain_tree(2))
    f, g = slots(line)
    direct = comp2(line, 0, identity(line, f), g)
    target = identity(line, comp2(line, 0, f, g))
    assert infer(line, direct) == infer(line, target)
    assert reading(line, direct, {}) == 1
    assert reading(line, translate_word(line, direct), {}) == reading(line, target, {}) == 0


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
    totals = [check_rank(r, args.agda_dir) for r in range(1, 5)]
    compare_readings()
    print('Checked equation counts', [n for n, _ in totals], 'and',
          sum(m for _, m in totals), 'mixed products at their translated faces.')
    print('The two-cell model separates the direct right whisker from its padded interpretation.')
