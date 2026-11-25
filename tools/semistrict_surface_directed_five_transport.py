"""Check both fixed-factor changes for a 4-declaration with compound attaching terms."""
from argparse import ArgumentParser
from pathlib import Path

from catt import arr, comp2, disc_tree, glue_tree, infer, maximal_vars, src, subst_tm, subst_ty, tdim, tdim_tm, tgt, tree_ctx, ucomp, v
from catt_unit_ordered_exchange import temporal_words
from ct_suspension import ident, susp_ctx, susp_tm
from relative_coherence_exchange_faces import head
from semistrict_surface_computad_folds import lift
from semistrict_surface_directed_power_queries import apply, crossing, loop, square
from semistrict_surface_directed_square_return import right_unit_at
from semistrict_surface_guarded_strip import faces as guarded_faces
from semistrict_surface_inverse_completion import DerivationEmitter
from semistrict_surface_positional_tags import loop_tower
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


def check_separated_loop(emitter):
    rect, raw_loop = loop()
    ctx = tree_ctx((((), ()), ((), ()), disc_tree(3)))
    *gates, z = map(v, maximal_vars(ctx))
    h = apply(ctx, (rect, raw_loop), gates)
    u_end = tgt(ctx, src(ctx, h))
    v_start = src(ctx, src(ctx, z))
    left_edge, right_edge = tgt(ctx, u_end), src(ctx, v_start)
    x = comp2(ctx, 1, comp2(ctx, 0, h, right_edge), comp2(ctx, 0, left_edge, v_start))
    y = comp2(ctx, 1, comp2(ctx, 0, u_end, right_edge), comp2(ctx, 0, left_edge, z))
    early, late = temporal_words(ctx, x, y, 2, 3)
    assert infer(ctx, early) == infer(ctx, late)

    # Follow the rank-four factors of the actual syntax. The return on the
    # base rectangle has equal strict 3-faces by outer subdivision (R81).
    inner_arity, inner = square(3)
    return_type = raw_loop[3][maximal_vars(raw_loop[1])[-1]][2]

    def letters(t):
        if tdim_tm(ctx, t) < 4:
            return []
        if t == z:
            return ['globe']
        _, arity, ty, labels = t
        if (arity, ty) == (inner_arity, inner[2]):
            return ['inner exchange']
        if (arity, ty) == (rect, return_type):
            return []
        assert ty == ucomp(arity)[2] and len(maximal_vars(arity)) == 2
        return [letter for j in maximal_vars(arity) for letter in letters(labels[j])]

    assert letters(early) == ['inner exchange', 'globe']
    assert letters(late) == ['globe', 'inner exchange']
    change = crossing(ctx, x, y)
    emitter.check_type('exchangeAcrossGlobe', ctx, change, arr(infer(ctx, late), late, early))
    # Change the written loop on each side of the separator, leaving its
    # placement fixed. The cut-two whisker uses the other input at rank three.
    for name, order in [('Before', True), ('After', False)]:
        for suffix, expand in [('Expand', True), ('Contract', False)]:
            fit = right_unit_at(ctx, x, expand)
            if order:
                placed = comp2(ctx, 2, fit, src(ctx, y))
                comparison = comp2(ctx, 3, placed, comp2(ctx, 2, tgt(ctx, x), y))
            else:
                placed = comp2(ctx, 2, fit, tgt(ctx, y))
                comparison = comp2(ctx, 3, comp2(ctx, 2, src(ctx, x), y), placed)
            ends = [src(ctx, comparison), tgt(ctx, comparison)]
            assert ends[0 if expand else 1] == (early if order else late)
            padded = tgt(ctx, fit) if expand else src(ctx, fit)
            assert ends[1 if expand else 0] == temporal_words(ctx, padded, y, 2, 3)[0 if order else 1]
            emitter.check_type(name.lower() + suffix, ctx, comparison, arr(infer(ctx, ends[0]), *ends))


def check_terminal_fold():
    tower = loop_tower(3)
    for ctx, value in [loop(), square(3)]:
        fold = tuple(v(tdim(ty) + 1) for ty in ctx)
        assert all(infer(tower, image) == subst_ty(ty, fold)
                   for ty, image in zip(ctx, fold, strict=True))
        fit = right_unit_at(ctx, value, True)
        folded = subst_tm(fit, fold)
        for side, given in [(2, src(ctx, fit)), (3, tgt(ctx, fit))]:
            assert lift(ctx, tower, fold, folded, given, 4, side) == fit

    ctx, direct, pasted = guarded_faces()
    fold = tuple(v(tdim(ty) + 1) for ty in ctx)
    folded = [subst_tm(term, fold) for term in (direct, pasted)]
    assert folded[0] != folded[1] and infer(tower, folded[0]) == infer(tower, folded[1])
    for term, folded_face in zip((direct, pasted), folded, strict=True):
        for side, given in [(2, src(ctx, term)), (3, tgt(ctx, term))]:
            assert lift(ctx, tower, fold, folded_face, given, 3, side) == term


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = DerivationEmitter()
    check(emitter)
    check_separated_loop(emitter)
    check_terminal_fold()
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        source = emitter.module('DirectedFiveTransport', __doc__)
        (args.agda_dir / 'DirectedFiveTransport.agda').write_text(
            source.replace('open import CaTTExp.Pure\n',
                           'open import CaTTExp.Gray.Pure\n'
                           'open import CaTTExp.Pure using (∅)\n'
                           'open import CaTTExp.PastingCheck ∅ using () renaming (checkPs to pastable)\n'))
    print('Checked prism and separator placements, fitted 5-rules, and eight lifts from the terminal 3-skeleton.')


if __name__ == '__main__':
    main()
