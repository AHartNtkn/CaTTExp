"""Check serialization with an inner exchange and round-trip transport across a higher attachment."""
from argparse import ArgumentParser
from itertools import combinations, permutations
from pathlib import Path

from catt import (arr, chain_tree, comp2, disc_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, subst_ty, tdim_tm, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident, susp_tm
from relative_coherence_exchange_faces import composite, head, string_tree
from semistrict_surface_directed_power_queries import apply, square
from semistrict_surface_inverse_completion import DerivationEmitter
from semistrict_surface_positional_tags import loop_tower
from semistrict_surface_top_forests import change_at_face
from semistrict_surface_top_string_tester import check_map


def occurrences(ctx, term, rank):
    if tdim_tm(ctx, term) < rank:
        return []
    if term[0] == 'v':
        return [term[1]] if tdim_tm(ctx, term) == rank else []
    return [i for arg in term[3] for i in occurrences(ctx, arg, rank)]


def check_pair_retractions(emitter):
    # The second update in the first slot has two versions joined by a 4-globe.
    ctx = tree_ctx(((((), ((),)), chain_tree(1), chain_tree(2)),))
    tips = list(map(v, maximal_vars(ctx)))
    sites = (0, 0, 1, 2, 2)
    test = tree_ctx(string_tree(1, (3, 3)))
    left, right = map(v, maximal_vars(test))
    fixed = [src(test, src(test, left)), tgt(test, src(test, left)), tgt(test, src(test, right))]
    retractions = {}
    for i, j in combinations(range(5), 2):
        if sites[i] == sites[j]:
            continue
        labels = []
        for k, tip in enumerate(tips):
            if sites[k] in (sites[i], sites[j]):
                ix, label = (i, left) if sites[k] == sites[i] else (j, right)
                if k != ix:
                    label = ident(test, (src if k < ix else tgt)(test, label))
            else:
                edge = fixed[int(sites[k] > sites[i]) + int(sites[k] > sites[j])]
                label = ident(test, ident(test, edge))
            if tdim_tm(ctx, tip) == 4:
                label = ident(test, label)
            labels.append(label)
        sigma = sub_from(ctx, test, dict(zip(maximal_vars(ctx), labels, strict=True)))
        check_map(ctx, test, sigma)
        retractions[i, j] = sigma

    for version in (src, tgt):
        moves = tips.copy()
        moves[1] = version(ctx, tips[1])
        signatures = set()
        for order in permutations(range(5)):
            if order.index(0) > order.index(1) or order.index(3) > order.index(4):
                continue
            state = [src(ctx, moves[k]) for k in (0, 2, 3)]
            path = []
            for k in order:
                state[sites[k]] = moves[k]
                path.append(composite(ctx, 1, state))
                state[sites[k]] = tgt(ctx, moves[k])
            history = composite(ctx, 2, path)
            signature = []
            for (i, j), sigma in retractions.items():
                projected = subst_tm(history, sigma)
                named = occurrences(test, projected, 3)
                expected = [left[1], right[1]] if order.index(i) < order.index(j) else [right[1], left[1]]
                assert named == expected
                signature.append(tuple(named))
                if emitter and (i, j) == (1, 3) and order == (3, 0, 1, 2, 4):
                    emitter.check_type('retract' + version.__name__, test, projected, infer(test, projected))
            signatures.add(tuple(signature))
        assert len(signatures) == 30


def check_schedules(size, emitter):
    ctx = tree_ctx((((chain_tree(size),), disc_tree(1)),))
    *changes, fixed = map(v, maximal_vars(ctx))
    native = susp_tm(square(2)[1])
    template = native[1], native
    current = src(ctx, changes[0])
    initial = src(ctx, apply(ctx, template, (current, fixed)))
    final = tgt(ctx, apply(ctx, template, (tgt(ctx, changes[-1]), fixed)))
    generic = head(ctx, initial, final)
    for pos in range(size + 1):
        pieces = []
        for i in range(size + 1):
            stage = src(ctx, changes[i]) if i < size else tgt(ctx, changes[-1])
            if i == pos:
                pieces.append(apply(ctx, template, (stage, fixed)))
            if i < size:
                face = src if i < pos else tgt
                pieces.append(change_at_face(ctx, template, face, 0, changes[i], (stage, fixed)))
        ports = [occurrences(ctx, p, 4) for p in pieces]
        assert ports == [[x[1]] for x in changes[:pos]] + [[]] + [[x[1]] for x in changes[pos:]]
        serial = composite(ctx, 3, pieces)
        assert infer(ctx, serial) == infer(ctx, generic)
        if emitter is not None and size == 2:
            for label, a, b in [('toSerial', generic, serial), ('fromSerial', serial, generic)]:
                comparison = head(ctx, a, b)
                emitter.check_type(label + str(pos), ctx, comparison, arr(infer(ctx, a), a, b))


def check_return(emitter):
    base = loop_tower(2)
    p = comp2(base, 1, v(2), v(2))
    ty = arr(infer(base, p), p, p)
    a = v(len(base))
    base += (ty,)
    line = tree_ctx(string_tree(2, (3, 3, 3)))
    x, y, end = map(v, maximal_vars(line))
    pair = comp2(line, 2, x, y)
    biased = comp2(line, 2, pair, end)
    generic = ucomp(line)
    rho, back = head(line, generic, biased), head(line, biased, generic)

    def actual(term):
        return apply(base, (line, term), (a, a, a))

    start = actual(generic)
    z = v(len(base))
    old = base + (arr(ty, start, start),)
    zz = comp2(old, 3, z, z)
    up = v(len(old))
    old += (arr(infer(old, z), zz, z),)
    new = base
    fold = list(map(v, range(len(base))))

    def declare(attachment, image):
        nonlocal new
        assert infer(old, image) == subst_ty(attachment, tuple(fold))
        name = v(len(new))
        new += (attachment,)
        fold.append(image)
        return name

    def gate(s, t, image):
        return declare(arr(infer(new, s), s, t), image)

    pair_name, triple_name, final_name = [declare(ty, actual(term)) for term in (pair, biased, generic)]
    after_pair = comp2(new, 2, pair_name, a)
    p_to = gate(actual(pair), pair_name, actual(ident(line, pair)))
    t_to = gate(after_pair, triple_name, actual(ident(line, biased)))
    last = gate(triple_name, final_name, actual(back))
    centre = gate(final_name, final_name, z)
    first = gate(final_name, triple_name, actual(rho))
    t_from = gate(triple_name, after_pair, actual(ident(line, biased)))
    p_from = gate(pair_name, actual(pair), actual(ident(line, pair)))
    entrance = composite(new, 3, (actual(rho), comp2(new, 2, p_to, a), t_to, last))
    leave = composite(new, 3, (first, t_from, comp2(new, 2, p_from, a), actual(back)))
    translated = composite(new, 3, (entrance, centre, leave))
    trip = subst_tm(translated, tuple(fold))

    # Compute the returned loops generically, before the three labels are identified.
    pair_action = comp2(line, 2, ident(line, pair), end)
    unit = ident(line, generic)
    l_loop = composite(line, 3, (rho, pair_action, ident(line, biased), back))
    r_loop = composite(line, 3, (rho, ident(line, biased), pair_action, back))
    assert subst_tm(entrance, tuple(fold)) == actual(l_loop)
    assert subst_tm(leave, tuple(fold)) == actual(r_loop)
    assert trip == composite(old, 3, (actual(l_loop), z, actual(r_loop)))

    globe = tree_ctx(disc_tree(4))
    single = v(maximal_vars(globe)[0])
    padded = composite(globe, 3, (ident(globe, src(globe, single)), single, ident(globe, tgt(globe, single))))

    def correction(shrink):
        l, r = actual(l_loop), actual(r_loop)
        identity = actual(unit)
        lfit = actual(head(line, l_loop, unit) if shrink else head(line, unit, l_loop))
        rfit = actual(head(line, r_loop, unit) if shrink else head(line, unit, r_loop))
        left = comp2(old, 3, comp2(old, 3, lfit, z), r)
        right = comp2(old, 3, comp2(old, 3, identity, z), rfit)
        pad = head(globe, padded, single) if shrink else head(globe, single, padded)
        finish = apply(old, (globe, pad), (z,))
        return composite(old, 4, (left, right, finish) if shrink else (finish, right, left))

    shrink, expand = correction(True), correction(False)
    assert (src(old, shrink), tgt(old, shrink)) == (trip, z)
    assert (src(old, expand), tgt(old, expand)) == (z, trip)
    both = comp2(old, 4, comp2(old, 3, shrink, trip), comp2(old, 3, z, shrink))
    returned_upper = composite(old, 4, (both, up, expand))
    translated_twice = comp2(new, 3, translated, translated)
    upper_type = arr(infer(new, translated), translated_twice, translated)
    new_up = declare(upper_type, returned_upper)
    forward = tuple(map(v, range(len(base)))) + (translated, new_up)
    check_map(old, new, forward)
    check_map(new, old, tuple(fold))
    # Extend once more with parallel 5-globes and a change between them.
    # The returned 6-rule has the same two collars on its two 5-faces.
    second = v(len(old))
    old += (infer(old, up),)
    highest = v(len(old))
    old += (arr(infer(old, up), up, second),)
    returned_second = composite(old, 4, (both, second, expand))
    second_name = declare(upper_type, returned_second)
    returned_highest = comp2(old, 4, comp2(old, 4, both, highest), expand)
    highest_name = declare(arr(upper_type, new_up, second_name), returned_highest)
    check_map(old, new, forward + (second_name, highest_name))
    check_map(new, old, tuple(fold))
    assert occurrences(old, returned_highest, 6) == [highest[1]]
    if emitter is not None:
        emitter.check_type('returnedChange', old, trip, infer(old, z))
        emitter.check_type('shrinkRoundTrip', old, shrink, arr(infer(old, z), trip, z))
        emitter.check_type('expandRoundTrip', old, expand, arr(infer(old, z), z, trip))
        emitter.check_type('liftUpperRuleBack', old, returned_upper, subst_ty(upper_type, tuple(fold)))
        emitter.check_type('returnAtCollaredFiveFaces', old, returned_highest,
                           arr(infer(old, returned_upper), returned_upper, returned_second))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = DerivationEmitter() if args.agda_dir else None
    check_pair_retractions(emitter)
    for size in range(1, 7):
        check_schedules(size, emitter)
    check_return(emitter)
    if emitter is not None:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('DirectedPorts', __doc__).replace(
            'open import CaTTExp.Pure\n', 'open import CaTTExp.Gray.Pure\n'
            'open import CaTTExp.Pure using (∅)\n'
            'open import CaTTExp.PastingCheck ∅ using () renaming (checkPs to pastable)\n')
        (args.agda_dir / 'DirectedPorts.agda').write_text(module)
    print('Checked 480 pair projections, 27 serial placements, and round-trip transport at higher rules.')


if __name__ == '__main__':
    main()
