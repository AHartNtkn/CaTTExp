"""Check the disc split on raw boundaries and binary operations."""

from collections import Counter
from functools import cache

from catt import (STAR, arr, comp2, disc_tree, glue_tree, infer, maximal_vars,
                  ps_dim, sub_from, subst_tm, subst_ty, tdim, tree_ctx, v)
from relative_coherence_hidden_seam import identity


@cache
def split(rank):
    disc = tree_ctx(disc_tree(rank))
    pair = tree_ctx(glue_tree(rank, rank - 1, rank))
    x, y = map(v, maximal_vars(pair))
    z = v(len(disc) - 1)
    generic = comp2(pair, rank - 1, x, y)
    exterior = sub_from(disc, pair, {z[1]: generic})
    plug = sub_from(pair, disc, {x[1]: z, y[1]: identity(disc, disc[-1][3])})
    composed = tuple(subst_tm(t, plug) for t in exterior)
    assert composed[:-1] == tuple(map(v, range(len(disc) - 1)))
    assert composed[-1] == comp2(disc, rank - 1, z, identity(disc, disc[-1][3]))
    return pair, exterior, plug


@cache
def translate_ty(ty, units):
    return STAR if ty == STAR else arr(translate_ty(ty[1], units),
                                       translate(ty[2], units), translate(ty[3], units))


@cache
def translate(t, units):
    if t[0] == 'v':
        return t
    _, ctx, old, args = t
    ty = translate_ty(old, units)
    args = tuple(translate(a, units) for a in args)
    n = tdim(ty) + 1
    if n == ps_dim(ctx) and ctx == tree_ctx(disc_tree(n)):
        if units:
            pair, exterior, plug = split(n)
            return 'coh', pair, subst_ty(ty, exterior), tuple(subst_tm(a, args) for a in plug)
        if ty == ctx[-1]:
            return args[-1]
    return 'coh', ctx, ty, args


def padded(ctx, term, times):
    ty = infer(ctx, term)
    if ty == STAR:
        return term
    for _ in range(times):
        term = comp2(ctx, tdim(ty), term, identity(ctx, ty[3]))
    return term


def check():
    counts = Counter()
    for n in range(1, 6):
        ctx = tree_ctx(disc_tree(n))
        z = v(len(ctx) - 1)
        args = tuple(map(v, range(len(ctx))))
        pair, exterior, plug = split(n)
        for i in range(3):
            for j in range(3):
                base, s, t = ctx[-1][1:]
                ty = arr(base, padded(ctx, s, i), padded(ctx, t, j))
                unary = ('coh', ctx, ty, args)
                assert infer(ctx, unary) == ty
                for units in (False, True):
                    result = translate(unary, units)
                    assert infer(ctx, result) == ty
                    assert translate(subst_tm(unary, exterior), units) == subst_tm(result, exterior)
                    if units:
                        assert result[1] == pair
                        assert subst_ty(result[2], plug) == ty
                    if ty == ctx[-1]:
                        assert result == (comp2(ctx, n - 1, z, identity(ctx, t)) if units else z)
                    elif not units:
                        assert result == unary
                    counts['typed disc translations and substitutions'] += 1

    for p in range(1, 6):
        for q in range(1, 6):
            for k in range(min(p, q)):
                ctx = tree_ctx(glue_tree(p, k, q))
                x, y = map(v, maximal_vars(ctx))
                term = comp2(ctx, k, x, y)
                for units in (False, True):
                    assert translate(term, units) == term
                    assert translate(identity(ctx, term), units) == identity(ctx, term)
                    counts['fixed binary heads and identities'] += 1
    for label, count in counts.items():
        print(f'{count} {label}')


if __name__ == '__main__':
    check()
