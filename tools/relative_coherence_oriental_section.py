"""Lift the aligned tetrahedral section and compare the returned shortcut at its exact type."""
from argparse import ArgumentParser
from itertools import combinations
from pathlib import Path

from canonical_gray_cube import build_cube
from catt import (STAR, arr, check_ctx, comp2, infer, src, subst_tm, subst_ty,
                  tgt, v)
from ct_suspension import ident
from emit_agda import Emitter
from rc2 import kappa, path
from relative_coherence_based_columns import Brackets
from relative_coherence_cut import top_counts
from relative_coherence_omission_carriers import instruction


def check(output):
    old, instructions = build_cube()
    ctx = old[:-1]
    paths = {tag: term for tag, term, _ in instructions if tag.startswith('path-')}
    routes = [term for tag, term, _ in instructions if tag.startswith('route-')]
    roots = [v((1 << i)-1) for i in range(4)]
    simplex = Brackets(4)
    atoms = {(i,): v(i) for i in range(4)}
    images = roots.copy()
    for i,j in combinations(range(4), 2):
        atoms[i,j] = simplex.bracket(v(i), v(j))
        digits = ''.join(str(axis) for axis in range(j,i,-1))
        images.append(paths[f'path-{roots[i][1]}-{digits}'])
    for i,j,k in combinations(range(4), 3):
        s = atoms[i,k]
        t = comp2(simplex.ctx, 0, atoms[i,j], atoms[j,k])
        atoms[i,j,k] = simplex.bracket(s,t)
        a, b = subst_tm(s, images), subst_tm(t, images)
        route = next(p for p in routes if src(ctx,p) == a and path(ctx,tgt(ctx,p)) == path(ctx,b))
        if tgt(ctx,route) != b:
            route = comp2(ctx, 1, route, kappa(ctx, tgt(ctx,route), b))
        assert infer(ctx,route) == arr(infer(ctx,a), a,b)
        images.append(route)
    s = comp2(simplex.ctx, 1, atoms[0,2,3], comp2(simplex.ctx, 0, atoms[0,1,2], atoms[2,3]))
    t = comp2(simplex.ctx, 1, atoms[0,1,3], comp2(simplex.ctx, 0, atoms[0,1], atoms[1,2,3]))
    s = comp2(simplex.ctx, 1, s, kappa(simplex.ctx, tgt(simplex.ctx,s), tgt(simplex.ctx,t)))
    top = simplex.bracket(s,t)
    wanted = subst_ty(simplex.ctx[top[1]], images)
    for new, prior in zip(wanted[2:], old[-1][2:]):
        assert top_counts(ctx,new) == top_counts(ctx,prior)
        assert all(path(ctx, f(ctx,new)) == path(ctx,f(ctx,prior)) for f in (src,tgt))
    ctx += (wanted,)
    images.append(v(len(ctx)-1))
    check_ctx(ctx)
    emitter = Emitter()
    for i, (term, ty) in enumerate(zip(images,simplex.ctx, strict=True)):
        expected = subst_ty(ty, images)
        assert infer(ctx,term) == expected
        if output:
            emitter.check_type('section'+str(i),ctx,term,expected)

    fold = []
    for i, ty in enumerate(ctx):
        if ty == STAR:
            low = next((axis for axis in range(3) if not i & (1 << axis)), 3)
            fold.append(v(low))
        elif ty[1] == STAR:
            a, b = (fold[u[1]] for u in ty[2:])
            fold.append(ident(simplex.ctx, a) if a == b else atoms[a[1],b[1]])
        else:
            break
    shortcut = atoms[0,3]
    returned = subst_tm(images[shortcut[1]], fold)
    assert returned != shortcut and path(simplex.ctx,returned) == path(simplex.ctx,shortcut)
    for tag, a, b in (('contract',returned,shortcut),('expand',shortcut,returned)):
        proof = kappa(simplex.ctx, a,b)
        ty = arr(infer(simplex.ctx,a), a,b)
        assert infer(simplex.ctx,proof) == ty
        if output:
            emitter.check_type(tag, simplex.ctx, proof, ty)
    if output:
        output.write_text(emitter.module(output.stem, 'Carried raw oriental section and returned shortcut.'))
    print('15 typed tetrahedral images, original cube top tableau, and both shortcut comparisons.')
    for k in (5,6):
        sizes = [len(instruction(k,face)) for face in combinations(range(k+1),5)]
        print(f'{k}-cube: four-simplex instructions have {sorted(set(sizes))} top tiles.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    check(parser.parse_args().agda)
