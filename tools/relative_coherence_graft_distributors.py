"""Check both F2 evaluations and their boundary-corrected raw distributor on a graft."""
from argparse import ArgumentParser
from pathlib import Path

from catt import (arr, comp2, fv_tm, fv_ty, infer, maximal_vars, restrict, sub_from,
                  subst_tm, tdim_tm, tree_ctx, ucomp, v)
from emit_agda import Emitter
from partial_cylinder_steiner import trees
from relative_coherence_exchange_faces import head
from relative_coherence_globe_padding import face


def comparison(ctx, a, b):
    ty = infer(ctx, a)
    assert ty == infer(ctx, b)
    support = fv_tm(a) | fv_ty(ty)
    assert support == fv_tm(b) | fv_ty(ty)
    small, inclusion = restrict(ctx, support)
    inverse = [None] * len(ctx)
    for i, term in enumerate(inclusion):
        inverse[term[1]] = v(i)
    generic = head(small, subst_tm(a, inverse), subst_tm(b, inverse))
    return subst_tm(generic, inclusion)


def distributor(tree, emitter=None, label=''):
    # The left maximal leaf is fixed; the right one is replaced by the tree.
    chart = tree_ctx((tree,))
    ctx = tree_ctx(((), tree))
    f, *entries = map(v, maximal_vars(ctx))
    slots = maximal_vars(chart)
    whole = ucomp(chart)
    original = sub_from(chart, ctx, dict(zip(slots, entries, strict=True)))
    first = comp2(ctx, 0, f, subst_tm(whole, original))
    acted = [comp2(ctx, 0, f, z) for z in entries]
    second = subst_tm(whole, sub_from(chart, ctx, dict(zip(slots, acted, strict=True))))
    parallel = infer(ctx, first) == infer(ctx, second)
    corrected = first
    for j in range(1, tdim_tm(ctx, first)):
        wanted = face(ctx, second, j, False)
        current = face(ctx, corrected, j, False)
        if wanted != current:
            corrected = comp2(ctx, j, comparison(ctx, wanted, current), corrected)
        wanted = face(ctx, second, j, True)
        current = face(ctx, corrected, j, True)
        if wanted != current:
            corrected = comp2(ctx, j, corrected, comparison(ctx, current, wanted))
    track = comparison(ctx, corrected, second)
    ty = arr(infer(ctx, second), corrected, second)
    assert infer(ctx, track) == ty
    if emitter:
        emitter.check_type('distribute'+label, ctx, track, ty)
        c = emitter.ctx(ctx)
        # Compare each output to the common full labelled graft. A pair of
        # failed computations cannot pass the check against idTree.
        expected = f'just (idTree (from-just (treeOf {c})))'
        for name, term in [('before', first), ('after', second), ('aligned', corrected)]:
            nm = name+label
            emitter.checks.append(f'{nm} : nf 30 {c} {emitter.tm(term)} ≡ {expected}\n{nm} = refl\n')
    return parallel


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--edges', type=int, default=5)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    values = [distributor(tree) for k in range(args.edges+1) for tree in trees(k)]
    print(f'{len(values)} grafts; {values.count(False)} required boundary repair.')
    # Two three-cells composed on the one-face already require alignment.
    branching = (((),), ((),))
    emitter = Emitter() if args.agda else None
    assert not distributor(branching, emitter, 'Branch')
    if emitter:
        module = emitter.module(args.agda.stem, 'Normal forms and the aligned graft distributor.')
        module = module.replace('open import CaTTExp.Pure', 'open import CaTTExp.Pure\nopen import CaTTExp.GlobularFiller using (nf; idTree)')
        args.agda.write_text(module)
