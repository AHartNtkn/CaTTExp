"""Check both fixed-factor changes for a 4-declaration with compound attaching terms."""
from argparse import ArgumentParser
from pathlib import Path

from catt import arr, comp2, disc_tree, glue_tree, infer, maximal_vars, src, tgt, tree_ctx, v
from ct_suspension import ident, susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from semistrict_surface_directed_power_queries import apply
from semistrict_surface_directed_square_return import right_unit_at
from semistrict_surface_realized_four import check_prism


def check_inverse_data(ctx, factor, emitter):
    disk = tree_ctx(disc_tree(2))
    slot = v(maximal_vars(disk)[0])
    expand = right_unit_at(disk, slot, True)
    contract = right_unit_at(disk, slot, False)
    for name, first, second in [('expanded', expand, contract), ('contracted', contract, expand)]:
        pair = comp2(disk, 2, first, second)
        unit = ident(disk, src(disk, first))
        for action, left, right in [('Insert', unit, pair), ('Cancel', pair, unit)]:
            result = apply(ctx, (disk, head(disk, left, right)), [factor])
            emitter.check_typed(name + action, ctx, result)


def fixed_factors(term, moving, arity, tips):
    if term[0] == 'v':
        return []
    _, shape, _, args = term
    if shape == arity and args[tips[1]] == moving:
        return [args[tips[0]]]
    return [factor for i in maximal_vars(shape)
            for factor in fixed_factors(args[i], moving, arity, tips)]


def check(emitter):
    p, prism = check_prism(False, emitter)
    lifted = susp_ctx(p), susp_tm(prism)
    emitter.check_typed('positiveCutPrism', *lifted)

    ctx = tree_ctx((disc_tree(1), disc_tree(2)))
    gate, step = map(v, maximal_vars(ctx))
    other = v(len(ctx))
    ctx += (infer(ctx, step),)
    fixed = comp2(ctx, 0, gate, src(ctx, src(ctx, step)))
    initial = comp2(ctx, 0, tgt(ctx, gate), step)
    final = comp2(ctx, 0, tgt(ctx, gate), other)
    padded_initial = comp2(ctx, 2, initial, ident(ctx, tgt(ctx, initial)))
    moving = v(len(ctx))
    attachment = arr(infer(ctx, initial), padded_initial, final)
    second_name = v(len(ctx) + 1)
    ctx += (attachment, attachment)
    enter = right_unit_at(ctx, initial, True)
    leave = right_unit_at(ctx, final, True)
    boundary = arr(infer(ctx, initial), initial, tgt(ctx, leave))
    for name, label in [('firstTag', moving), ('secondTag', second_name)]:
        fitted = comp2(ctx, 3, comp2(ctx, 3, enter, label), leave)
        emitter.check_type(name, ctx, fitted, boundary)

    check_inverse_data(ctx, fixed, emitter)

    expand = right_unit_at(ctx, fixed, True)
    contract = right_unit_at(ctx, fixed, False)
    wing = tree_ctx(glue_tree(2, 1, 4))
    tips = maximal_vars(wing)
    for name, change in [('expandFixed', expand), ('contractFixed', contract)]:
        paste = apply(ctx, lifted, (change, moving))
        before, after = src(ctx, paste), tgt(ctx, paste)
        assert fixed_factors(before, moving, wing, tips) == [src(ctx, change)]
        assert fixed_factors(after, moving, wing, tips) == [tgt(ctx, change)]
        emitter.check_type(name, ctx, paste, arr(infer(ctx, before), before, after))

    # Fit a top attachment at the two literal 4-faces of the second prism.
    # Unit fits on a 4-disc use the 5-variable at its actual padded boundary.
    reverse = v(len(ctx))
    outgoing = right_unit_at(ctx, before, False)
    incoming = right_unit_at(ctx, after, True)
    ctx += (arr(infer(ctx, after), tgt(ctx, incoming), src(ctx, outgoing)),)
    return_term = comp2(ctx, 4, comp2(ctx, 4, incoming, reverse), outgoing)
    emitter.check_type('returnAtSpecifiedFaces', ctx, return_term,
                       arr(infer(ctx, after), after, before))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    check(emitter)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        source = emitter.module('DirectedFiveTransport', __doc__)
        (args.agda_dir / 'DirectedFiveTransport.agda').write_text(
            source.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))
    print('Checked the fixed factors on both prism boundaries, four inverse fits, and the fitted 5-rule.')


if __name__ == '__main__':
    main()
