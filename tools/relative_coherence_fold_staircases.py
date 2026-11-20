"""Check lower face ranks in partial cylinders and return through nested fold staircases."""
from argparse import ArgumentParser
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, disc_tree, fv_ty, infer, maximal_vars, src,
                  sub_from, subst_tm, tdim, tdim_tm, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_branch_comparisons import cylinder
from partial_cylinder_steiner import trees
from relative_coherence_exchange_faces import head
from relative_coherence_globe_padding import face


def lowest_written_face(ctx):
    lowest = None
    for ty in ctx:
        while ty != STAR:
            rank = tdim(ty)
            if any(z[0] != 'v' for z in ty[2:]):
                lowest = rank if lowest is None else min(lowest, rank)
            ty = ty[1]
    return lowest


def check_cylinders(size):
    checked = 0
    for k in range(size + 1):
        for tree in trees(k):
            ctx = tree_ctx(tree)
            for mask in range(1, 1 << len(ctx)):
                marks = {i for i in range(len(ctx)) if mask & (1 << i)}
                if any(i not in marks and fv_ty(ty) & marks for i, ty in enumerate(ctx)):
                    continue
                extended, _, _ = cylinder(ctx, marks)
                lowest = lowest_written_face(extended)
                floor = min(tdim(ctx[i]) + 1 for i in marks) + 1
                assert lowest is None or lowest >= floor
                checked += 1
    return checked



def check_knot():
    # A weakly attached three-globe with a globular two-skeleton.
    globe = tree_ctx(disc_tree(3))
    lower = globe[:-1]
    alpha, beta = globe[-1][2:]
    f, parallel = infer(lower, alpha)[2:]
    disk = tree_ctx(disc_tree(1))
    labels = sub_from(disk, lower, {2: f})
    wrapped = head(disk, v(0), v(1))
    adjust = subst_tm(head(disk, wrapped, v(2)), labels)
    a, b = (comp2(lower, 1, adjust, z) for z in (alpha, beta))
    original = lower + (arr(infer(lower, a), a, b),)
    knot = v(len(lower))
    subdivided = lower + (infer(lower, a),)
    subdivided += (arr(infer(lower, a), a, knot), arr(infer(lower, b), knot, b))
    check_ctx(original)
    check_ctx(subdivided)
    assert infer(lower, a)[2:] == (subst_tm(wrapped, labels), parallel)
    assert lowest_written_face(lower) is None
    assert lowest_written_face(original) == lowest_written_face(subdivided) == 1

def attach(ctx, term, prefix, factors):
    for cut, factor in factors:
        term = comp2(ctx, cut, factor, term) if prefix else comp2(ctx, cut, term, factor)
    return term


def peel(ctx, comparison, a, b, prefix, factors):
    """Undo each outer factor; align every exposed pole on the test's pasting support."""
    n = tdim_tm(ctx, a)
    for pos in reversed(range(len(factors))):
        cut, k = factors[pos]
        inner_a, inner_b = (attach(ctx, z, prefix, factors[:pos]) for z in (a, b))
        inverse = head(ctx, tgt(ctx, k), src(ctx, k))
        comparison = attach(ctx, comparison, prefix, [(cut, inverse)])
        for j in range(cut + 1, n + 1):
            start = face(ctx, inner_a, j, False)
            end = face(ctx, inner_b, j, True)
            left = head(ctx, start, face(ctx, comparison, j, False))
            right = head(ctx, face(ctx, comparison, j, True), end)
            comparison = comp2(ctx, j, comp2(ctx, j, left, comparison), right)
        assert infer(ctx, comparison)[2:] == (inner_a, inner_b)
    return comparison


def check_return(n, free_target, emitter):
    # The other square remains stationary throughout. Its top arrow survives the fold.
    ctx = tree_ctx((disc_tree(1), disc_tree(1)))
    link, other = map(v, maximal_vars(ctx))
    held = src(ctx, link) if free_target else tgt(ctx, link)
    small = tree_ctx(((), disc_tree(1)))
    edge, square = map(v, maximal_vars(small))
    fold = sub_from(ctx, small, {link[1]: ident(small, edge), other[1]: square})
    include = sub_from(small, ctx, {edge[1]: held, square[1]: other})
    endo = tuple(subst_tm(t, include) for t in fold)

    a = ucomp(ctx)
    b = comp2(ctx, 1, comp2(ctx, 0, link, src(ctx, other)),
              comp2(ctx, 0, tgt(ctx, link), other))
    prefix, suffix = [], []
    if free_target:
        suffix.append((1, comp2(ctx, 0, link, tgt(ctx, other))))
    else:
        prefix.append((1, comp2(ctx, 0, link, src(ctx, other))))

    def stairs(z):
        folded = subst_tm(z, endo)
        lo, hi = (folded, z) if free_target else (z, folded)
        return attach(ctx, lo, False, suffix), attach(ctx, hi, True, prefix)

    for d in range(2, n):
        ka, kb = (head(ctx, *stairs(z)) for z in (a, b))
        prefix.append((d, ka))
        suffix.append((d, kb))
        p = head(ctx, a, b)
        a, b = p, comp2(ctx, d, p, ident(ctx, b))
    assert a != b
    folded = head(small, subst_tm(a, fold), subst_tm(b, fold))
    transferred = subst_tm(folded, include)
    sa, ta = stairs(a)
    sb, tb = stairs(b)
    if free_target:
        before, after = head(ctx, ta, sa), head(ctx, sb, tb)
        middle = attach(ctx, transferred, False, suffix)
        factors = prefix
    else:
        before, after = head(ctx, sa, ta), head(ctx, tb, sb)
        middle = attach(ctx, transferred, True, prefix)
        factors = suffix
    comparison = comp2(ctx, n, comp2(ctx, n, before, middle), after)
    result = peel(ctx, comparison, a, b, free_target, factors)
    expected = arr(infer(ctx, a), a, b)
    assert infer(ctx, result) == expected and len(factors) == n - 2
    if emitter:
        title = 'target' if free_target else 'source'
        emitter.check_type(title + str(n), ctx, result, expected)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--edges', type=int, default=4)
    parser.add_argument('--rank', type=int, default=4)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.rank < 3:
        parser.error('rank must be at least three')
    check_knot()
    count = check_cylinders(args.edges)
    print(f'Checked all iterated face ranks in {count} marked pasting contexts.', flush=True)
    emitter = Emitter() if args.agda else None
    for rank in range(3, args.rank + 1):
        for free_target in (False, True):
            check_return(rank, free_target, emitter if rank == args.rank else None)
        print(f'Returned through both staircases in input rank {rank}.', flush=True)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Two-sided fold staircase checks.'))
