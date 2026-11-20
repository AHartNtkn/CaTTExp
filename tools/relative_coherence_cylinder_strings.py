"""Retract full-cylinder top strings and verify the single marked input in the mixed pair."""
from argparse import ArgumentParser
from pathlib import Path

from catt import arr, comp2, fv_tm, infer, maximal_vars, ps_dim, subst_tm, subst_ty, tdim, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from gray_constant_cylinder import correction
from gray_globe_branch_comparisons import cylinder
from gray_partial_cylinder_sections import selections
from gray_temporal_partial_actions import action, rails
from partial_cylinder_steiner import trees
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import string_tree


def contract(tree, emitter=None):
    old = tree_ctx(tree)
    ctx, minus, mix = cylinder(old, set(range(len(old))))
    plus = [v(t[1]+1) for t in minus]
    rank = ps_dim(old)
    anchor = list(range(len(old)))
    arrows = []
    for i,ty in enumerate(old):
        if tdim(ty)+1 == rank:
            b, c = ty[2][1], ty[3][1]
            assert b < c < i and anchor[c] == c
            anchor[c] = anchor[b]
            arrows.append(i)
    rho = [None]*len(ctx)
    kept = set()
    h = {i:mix[j] for i,j in enumerate(anchor) if i not in arrows}
    for i in range(len(old)):
        if i in arrows:
            start, finish = (u[1] for u in old[i][2:])
            j = anchor[start]
            assert anchor[finish] == j
            for copy in (minus,plus):
                rho[copy[i][1]] = ident(ctx,copy[j])
            # Both padded endpoints contract to the very same mixed generator.
            def comparison(side, rev):
                copy = (minus,plus)[side]
                return correction(ctx, copy[j], rails(old,v(i),h,side),side,rev)
            rho[mix[i][1]] = comp2(ctx, rank, comparison(0,False), comparison(1,True))
            reverse = comp2(ctx, rank, comparison(1,False), comparison(0,True))
            native_type = ctx[mix[i][1]]
            # The terminal mixed two-slot occurs once and on only one side.
            assert top_counts(ctx,native_type[2])[mix[finish][1]] == 1
            assert not top_counts(ctx,native_type[3])[mix[finish][1]]
            ends = [subst_tm(t,rho) for t in native_type[2:]]
            expected = arr(infer(ctx,ends[0]),*ends)
            rev_type = arr(expected[1],*reversed(ends))
            assert infer(ctx,reverse) == rev_type
            if emitter:
                emitter.check_type('collapse'+str(i),ctx,rho[mix[i][1]],expected)
                emitter.check_type('reverse'+str(i),ctx,reverse,rev_type)
        else:
            j = anchor[i]
            for family in (minus,plus,mix):
                rho[family[i][1]] = family[j]
                kept.add(family[j][1])
    for i,ty in enumerate(ctx):
        assert infer(ctx,rho[i]) == subst_ty(ty,rho)
        assert fv_tm(rho[i]) <= kept
        if i in kept:
            assert rho[i] == v(i)
    return len(arrows), len(ctx)


def temporal_slots():
    tree = string_tree(2,(3,3))
    old = tree_ctx(tree)
    slots = maximal_vars(old)
    count = 0
    for marks in selections(old):
        if not marks or any(tdim(old[i])+1 < 2 for i in marks):
            continue
        term, ctx, _ = action(tree,marks)
        _, _, change = cylinder(old,marks)
        for i in slots:
            if i in marks:
                assert top_counts(ctx,term)[change[i][1]] == 1
                count += 1
    return count


def main(bound, output):
    totals = [0,0,0]
    for size in range(bound+1):
        for tree in trees(size):
            if ps_dim(tree_ctx(tree)) != 3:
                continue
            pairs, entries = contract(tree)
            totals = [a+b for a,b in zip(totals,(1,pairs,entries))]
    print(f'{totals[0]} full cylinders, {totals[1]} contracted spatial arrows, {totals[2]} typed substitution entries.')
    for rank in (2,4,5):
        n,entries = contract(string_tree(rank-1,(rank,rank)))
        print(f'Rank {rank}: {n} collapsed string arrows, {entries} typed entries.')
    print(f'{temporal_slots()} exact mixed top-slot counts on the binary temporal chart.')
    emitter = Emitter() if output else None
    contract(string_tree(2,(3,3)),emitter)
    if emitter:
        output.write_text(emitter.module(output.stem,'Contraction of two spatial steps and their reverse cap comparisons.'))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--bound',type=int,default=6)
    parser.add_argument('--agda',type=Path)
    args = parser.parse_args()
    main(args.bound,args.agda)
