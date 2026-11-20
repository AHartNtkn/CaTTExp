"""Check the two cap divisions and a full-cylinder labelling with different old endpoints."""
from argparse import ArgumentParser
from functools import reduce
from pathlib import Path

from catt import STAR, arr, comp2, disc_tree, fv_ty, infer, maximal_vars, sub_from, subst_ty, tdim, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_branch_comparisons import cylinder
from gray_temporal_partial_actions import chart_comparison, pad
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head


def inspect(n, output):
    disk = tree_ctx(disc_tree(n))
    top = maximal_vars(disk)[0]
    domain, minus, mixed = cylinder(disk, frozenset(range(len(disk))))
    plus = [v(t[1]+1) for t in minus]
    faces = domain[mixed[top][1]][2:]
    for sign, caps in enumerate((minus, plus)):
        unknown = caps[top][1]
        assert faces[sign] == pad(domain, disk, v(top), mixed, sign)(caps[top])
        assert top_counts(domain, faces[sign])[unknown] == 1
        assert not top_counts(domain, faces[1-sign])[unknown]
        assert unknown not in fv_ty(infer(domain, faces[sign]))

    tree = ((), ()) + disc_tree(n)
    chart = tree_ctx(tree)
    p, q, x = (v(i) for i in maximal_vars(chart))
    products = (comp2(chart, 0, p, comp2(chart, 0, q, x)),
                comp2(chart, 0, comp2(chart, 0, p, q), x))
    caps = [sub_from(disk, chart, {top:a}) for a in products]
    inner = sub_from(disk, chart, {top:x})
    changes = {}
    values = [None]*len(domain)
    for i, ty in enumerate(disk):
        a, b = [pad(chart, disk, v(i), changes, s)(cp[i]) for s,cp in enumerate(caps)]
        if ty == STAR:
            assert a == b
            h = ident(chart, a)
        else:
            dim = tdim(ty) + 1
            shape = ((), ()) + disc_tree(dim)
            h = chart_comparison(chart, shape, (p, q, inner[i]), a, b)
            if i == top:
                back = chart_comparison(chart, shape, (p, q, inner[i]), b, a)
                reverse_type = arr(infer(chart, b), b, a)
                assert infer(chart, back) == reverse_type
                if output:
                    output.check_type('back'+str(n), chart, back, reverse_type)
        changes[i] = h
        values[minus[i][1]], values[plus[i][1]], values[mixed[i][1]] = caps[0][i], caps[1][i], h
    assert caps[0][top] != caps[1][top]
    if n >= 2:
        assert infer(chart, caps[0][top]) != infer(chart, caps[1][top])
    for ty,t in zip(domain, values, strict=True):
        assert infer(chart,t) == subst_ty(ty, values)
    if output:
        output.check_type('mixed'+str(n), chart, changes[top], subst_ty(domain[mixed[top][1]], values))
    print(f'Rank {n}: both generic cap occurrences, {len(values)} substitution entries, both comparison types.')


def loop_frames(n):
    disk = tree_ctx(disc_tree(n))
    top = maximal_vars(disk)[0]
    ctx = (STAR,)
    tower = [v(0)]
    for _ in range(n-1):
        tower.append(ident(ctx,tower[-1]))
    loop_type = arr(infer(ctx,tower[-1]), tower[-1],tower[-1])
    ctx += (loop_type,)
    point = (STAR,)
    rail = {}
    for i, ty in enumerate(disk[:-1]):
        d = tdim(ty) + 1
        a,b = [pad(point,disk,v(i),rail,s)(tower[d]) for s in (0,1)]
        rail[i] = head(point,a,b)
    for k in (0,1,3,9):
        loop = (reduce(lambda a,b:comp2(ctx,n-1,a,b), [v(1)]*k)
                if k else ident(ctx,tower[-1]))
        a,b = [pad(ctx,disk,v(top),rail,s)(loop) for s in (0,1)]
        assert infer(ctx,a) == infer(ctx,b)
        assert all(top_counts(ctx, side)[1] == k for side in (a,b))
    print(f'Rank {n}: based powers 0, 1, 3, 9 retain their exact top multiplicity under both frames.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--height', type=int, default=5)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    for n in range(1, args.height+1):
        inspect(n, emitter if n<=4 else None)
        loop_frames(n)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Full walking cap divisions and typed reverse comparisons.'))
