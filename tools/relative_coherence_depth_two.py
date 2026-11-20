"""Check truncated depth-two cylinders and top lifts at both altered weak faces."""

from argparse import ArgumentParser
from collections import Counter
from itertools import combinations
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, fv_ty, glue_tree, infer, src,
                  subst_tm, tdim_tm, tgt, tree_ctx, v)
from emit_agda import Emitter
from gray_globe_branch_comparisons import cylinder
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head


def globular(ty):
    return ty == STAR or (ty[2][0] == 'v' and ty[3][0] == 'v')


def truncations():
    counts = Counter()
    for rank in (2, 3, 4):
        for tree in (disc_tree(rank), glue_tree(rank, rank - 1, rank),
                     glue_tree(rank, rank - 2, rank - 1)):
            old = tree_ctx(tree)
            eligible = [i for i in range(len(old)) if tdim_tm(old, v(i)) >= rank - 2]
            for size in range(1, len(eligible) + 1):
                for subset in combinations(eligible, size):
                    marks = set(subset)
                    if any(marks & fv_ty(ty) and i not in marks for i, ty in enumerate(old)):
                        continue
                    ctx, _, moves = cylinder(old, marks)
                    for i, ty in enumerate(ctx):
                        if globular(ty):
                            continue
                        level = tdim_tm(ctx, v(i))
                        assert level >= rank
                        if level == rank:
                            assert globular(ty[1]) and v(i) in moves.values()
                    counts['cylinders'] += 1
                    counts['nonglobular_at_cut'] += any(
                        not globular(ty) and tdim_tm(ctx, v(i)) == rank for i, ty in enumerate(ctx))
    return counts


def changed_faces(rank, emitter):
    disk = tree_ctx(disc_tree(rank))
    z = v(len(disk) - 1)
    c = head(disk, src(disk, z), tgt(disk, z))
    marks = {i for i in range(len(disk)) if tdim_tm(disk, v(i)) >= rank - 2}
    ctx, minus, changes = cylinder(disk, marks)
    plus = [v(t[1] + 1) if i in marks else t for i, t in enumerate(minus)]

    def staircase(term, incoming):
        face = z
        poles = []
        for _ in range(rank):
            face = src(disk, face) if incoming else tgt(disk, face)
            poles.append(face[1])
        for cut, i in enumerate(reversed(poles)):
            if i in changes:
                term = (comp2(ctx, cut, changes[i], term) if incoming else
                        comp2(ctx, cut, term, changes[i]))
        return term

    neg = staircase(subst_tm(c, minus), False)
    pos = staircase(subst_tm(c, plus), True)
    before = staircase(subst_tm(head(disk, c, z), minus), False)
    after = staircase(subst_tm(head(disk, z, c), plus), True)
    middle = changes[z[1]]
    assert neg != src(ctx, middle) and pos != tgt(ctx, middle)
    lift = comp2(ctx, rank, comp2(ctx, rank, before, middle), after)
    expected = arr(infer(ctx, neg), neg, pos)
    assert infer(ctx, lift) == expected and top_counts(ctx, lift) == {middle[1]: 1}
    emitter.check_typed(f'top-lift-{rank}', ctx, lift)
    emitter.check_type(f'top-lift-{rank}', ctx, lift, expected)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    results = truncations()
    print(f"{results['cylinders']} typed cylinders, {results['nonglobular_at_cut']} nonglobular at the cut")
    emitter = Emitter()
    for rank in (2, 3, 4, 5):
        changed_faces(rank, emitter)
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Depth-two lifts at adjusted faces.'))
    print('Four Gray top lifts at two altered faces checked')
