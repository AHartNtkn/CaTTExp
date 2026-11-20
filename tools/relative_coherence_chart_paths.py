"""Check proper-input chart paths against their literal CaTT comparisons."""

from argparse import ArgumentParser
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, disc_tree, fv_tm, glue_tree,
                  infer, maximal_vars, ps_boundary_vars, restrict, src, sub_from,
                  subst_tm, tdim_tm, tgt, tree_ctx, v)
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity


def unitor(ctx, term):
    tree = disc_tree(tdim_tm(ctx, term))
    disk = tree_ctx(tree)
    z = v(len(disk) - 1)
    padded = comp2(disk, tdim_tm(disk, z) - 1, z, identity(disk, tgt(disk, z)))
    return subst_tm(head(disk, z, padded), sub_from(disk, ctx, {z[1]: term}))


def two_triangles():
    ctx = (STAR,) * 5
    atoms = []
    for start, middle, end in [(0, 1, 2), (2, 3, 4)]:
        left, right, short = (v(len(ctx) + j) for j in range(3))
        ctx += (arr(STAR, v(start), v(middle)), arr(STAR, v(middle), v(end)),
                arr(STAR, v(start), v(end)))
        long = comp2(ctx, 0, left, right)
        atoms.append(v(len(ctx)))
        ctx += (arr(infer(ctx, long), long, short),)
    check_ctx(ctx)
    return ctx, atoms


def read_path(ctx, atoms, rank, term):
    # On these triangle charts the displayed whole mark uses both atoms.
    # A single proper slot always uses just one of the two.
    def marked(t):
        return all(a[1] in fv_tm(t) for a in atoms)

    _, arity, ty, sub = term
    if any(marked(t) for t in sub):
        return [edge for t in sub if marked(t) and tdim_tm(ctx, t) == rank + 1
                for edge in read_path(ctx, atoms, rank, t)]

    def name(sign, face):
        slots = ps_boundary_vars(arity, rank, sign)
        shape, inclusion = restrict(arity, slots)
        renumber = [None] * len(arity)
        for i, variable in enumerate(inclusion):
            renumber[variable[1]] = v(i)
        return (shape, subst_tm(face, renumber), tuple(sub[i] for i in sorted(slots)))

    return [(name('-', ty[2]), name('+', ty[3]))]


def check_rank(ctx, atoms, rank, emitter):
    cut = rank - 2
    moving = [unitor(ctx, a) for a in atoms]
    padded = [comp2(ctx, rank, h, identity(ctx, tgt(ctx, h))) for h in moving]
    comparisons = {}
    for i in range(2):
        for j in range(2):
            hs = [(moving, padded)[i][0], (moving, padded)[j][1]]
            arity = tree_ctx(glue_tree(rank + 1, cut, rank + 1))
            a, b = (v(k) for k in maximal_vars(arity))
            direct = comp2(arity, cut, a, b)
            lr = comp2(arity, rank, comp2(arity, cut, a, src(arity, b)),
                       comp2(arity, cut, tgt(arity, a), b))
            rl = comp2(arity, rank, comp2(arity, cut, src(arity, a), b),
                       comp2(arity, cut, a, tgt(arity, b)))
            sub = sub_from(arity, ctx, dict(zip(maximal_vars(arity), hs)))
            direct, lr_path, rl_path = (subst_tm(t, sub) for t in (direct, lr, rl))
            paths = [read_path(ctx, atoms, rank, t) for t in (direct, lr_path, rl_path)]
            assert [len(path) for path in paths] == [1, 2, 2]
            for path in paths[1:]:
                assert path[0][1] == path[1][0]
                assert (path[0][0], path[1][1]) == paths[0][0]
            assert paths[1][0][1] != paths[2][0][1]
            proof = subst_tm(head(arity, lr, rl), sub)
            expected = arr(infer(ctx, lr_path), lr_path, rl_path)
            assert infer(ctx, proof) == expected
            label = f'exchange-{rank}-{i}-{j}'
            emitter.check_typed(label, ctx, proof)
            emitter.check_type(label, ctx, proof, expected)
            comparisons[i, j] = (paths, direct)
    # Alter the proper comparisons without changing their raw m-ends.
    assert all(p == comparisons[0, 0][0] for p, _ in comparisons.values())
    assert len({d for _, d in comparisons.values()}) == 4
    # The direct product of both input (m+2)-unitors witnesses the change.
    higher = comp2(ctx, cut, *(unitor(ctx, h) for h in moving))
    expected = arr(infer(ctx, comparisons[0, 0][1]),
                   comparisons[0, 0][1], comparisons[1, 1][1])
    assert infer(ctx, higher) == expected
    emitter.check_typed(f'proper-{rank}', ctx, higher)
    emitter.check_type(f'proper-{rank}', ctx, higher, expected)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    ctx, atoms = two_triangles()
    for rank in (2, 3, 4):
        check_rank(ctx, atoms, rank, emitter)
        ctx, atoms = susp_ctx(ctx), [susp_tm(a) for a in atoms]
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Two proper factors in a chart.'))
    print('12 exchanges, 3 simultaneous input changes and 36 chart paths verified')
