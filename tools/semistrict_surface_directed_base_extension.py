"""Check a mixed prism and a compound reverse attachment outside the cut of the 2-skeleton."""
from argparse import ArgumentParser
from pathlib import Path

from catt import arr, comp2, disc_tree, infer, maximal_vars, src, subst_tm, sub_from, tgt, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head
from semistrict_surface_directed_power_queries import apply
from semistrict_surface_realized_four import check_prism


def pad(ctx, term, on_left):
    unit = ident(ctx, src(ctx, term) if on_left else tgt(ctx, term))
    return comp2(ctx, 2, unit, term) if on_left else comp2(ctx, 2, term, unit)


def unit_fit(ctx, term, on_left, expand):
    disk = tree_ctx(disc_tree(3))
    variable = v(maximal_vars(disk)[0])
    ends = variable, pad(disk, variable, on_left)
    return apply(ctx, (disk, head(disk, *(ends if expand else ends[::-1]))), [term])


def check(emitter):
    prism_ctx, prism = check_prism(False, emitter)
    s, t = src(prism_ctx, prism), tgt(prism_ctx, prism)
    fitted_prism = head(prism_ctx, pad(prism_ctx, s, False), pad(prism_ctx, t, True))
    emitter.check_typed('refittedPrism', prism_ctx, fitted_prism)

    ctx = tree_ctx((disc_tree(1), ()))
    alpha, edge = map(v, maximal_vars(ctx))
    unit = ident(ctx, edge)
    doubled = comp2(ctx, 1, unit, unit)
    change = v(len(ctx))
    ctx += (arr(infer(ctx, unit), doubled, unit),)
    labels = sub_from(prism_ctx, ctx, dict(zip(maximal_vars(prism_ctx), (alpha, change), strict=True)))
    old_s, old_t = (subst_tm(term, labels) for term in (s, t))
    forward = subst_tm(fitted_prism, labels)
    emitter.check_typed('mixedPrism', ctx, forward)
    assert src(ctx, forward) == pad(ctx, old_s, False)
    assert tgt(ctx, forward) == pad(ctx, old_t, True)
    back = v(len(ctx))
    ctx += (arr(infer(ctx, old_t), tgt(ctx, forward), src(ctx, forward)),)
    reverse = composite(ctx, 3, [unit_fit(ctx, old_t, True, True), back,
                                 unit_fit(ctx, old_s, False, False)])
    required = arr(infer(ctx, old_t), old_t, old_s)
    assert infer(ctx, back) != required and infer(ctx, reverse) == required
    emitter.check_type('returnAtOldFaces', ctx, reverse, required)

    # Read b's exterior version from each actual schedule: cut-zero with a
    # fixed edge places it there. The other 3-factors contain no b.
    def versions(term):
        if term[0] == 'v':
            return []
        _, arity, _, args = term
        tips = [args[i] for i in maximal_vars(arity)]
        if len(tips) == 2 and tips[1] == change:
            return [tips[0]]
        return [p for child in tips for p in versions(child)]

    assert versions(old_s) == [src(ctx, alpha)]
    assert versions(old_t) == [tgt(ctx, alpha)]


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    check(emitter)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        source = emitter.module('DirectedBaseExtension', __doc__)
        (args.agda_dir / 'DirectedBaseExtension.agda').write_text(
            source.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))
    print('Checked both exterior versions and the raw return at the two original faces.')


if __name__ == '__main__':
    main()
