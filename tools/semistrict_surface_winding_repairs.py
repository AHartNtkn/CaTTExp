"""Check insertion of a scalar winding into a repair at arbitrary globular faces."""
from argparse import ArgumentParser
from collections import Counter
from functools import reduce
from itertools import product
from pathlib import Path

from catt import STAR, arr, comp2, disc_tree, infer, maximal_vars, src, tgt, tree_ctx, v
from ct_suspension import susp_ctx, susp_tm, susp_ty
from emit_agda import Emitter
from relative_coherence_cut import Cut, top_counts
from relative_coherence_exchange_faces import string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_first_failure_gate import compare_on_disc, right_unit, unchanged
from semistrict_surface_weak_braid_gate import check_cube


def unitors(ctx, beta):
    start = compare_on_disc(ctx, src(ctx, beta), unchanged, right_unit)
    end = compare_on_disc(ctx, tgt(ctx, beta), right_unit, unchanged)
    return start, end


def carry(ctx, beta, scalar):
    left, right = unitors(ctx, beta)
    inside = comp2(ctx, 0, beta, scalar)
    return comp2(ctx, 1, comp2(ctx, 1, left, inside), right)


def double_unit(ctx, beta):
    f = tgt(ctx, tgt(ctx, beta))
    return identity(ctx, identity(ctx, f))


def padded(ctx, beta):
    return carry(ctx, beta, double_unit(ctx, beta))


def act(ctx, beta, scalar):
    opening = compare_on_disc(ctx, beta, unchanged, padded)
    closing = compare_on_disc(ctx, beta, padded, unchanged)
    return comp2(ctx, 2, comp2(ctx, 2, opening, carry(ctx, beta, scalar)), closing)


def stationary(ctx, beta):
    return act(ctx, beta, identity(ctx, double_unit(ctx, beta)))


def check_repair():
    ctx = tree_ctx(disc_tree(3))
    s, t = v(len(ctx) - 1), v(len(ctx))
    ctx += (ctx[-1],)
    beta = tgt(ctx, s)
    unit = double_unit(ctx, beta)

    def rule(a, b):
        nonlocal ctx
        assert infer(ctx, a) == infer(ctx, b)
        result = v(len(ctx))
        ctx += (arr(infer(ctx, a), a, b),)
        return result

    edge = src(ctx, unit)
    a, inverse = rule(edge, edge), rule(edge, edge)
    pair = comp2(ctx, 1, a, inverse)
    opening, closing = rule(unit, pair), rule(pair, unit)
    zero_word = comp2(ctx, 2, opening, closing)
    fit_zero = rule(identity(ctx, unit), zero_word)
    twist = rule(pair, pair)
    nonzero_word = comp2(ctx, 2, comp2(ctx, 2, opening, twist), closing)
    zero_start = comp2(ctx, 2, s, act(ctx, beta, zero_word))
    nonzero_start = comp2(ctx, 2, s, act(ctx, beta, nonzero_word))
    zero_rule = rule(zero_start, t)
    other_rule = rule(nonzero_start, t)
    return_fit = compare_on_disc(ctx, s, unchanged, right_unit)
    generic_fit = compare_on_disc(ctx, beta, identity, stationary)
    loop_fit = comp2(ctx, 3, generic_fit, act(ctx, beta, fit_zero))
    start_to_zero = comp2(ctx, 3, return_fit, comp2(ctx, 2, s, loop_fit))
    repair = comp2(ctx, 3, start_to_zero, zero_rule)
    expected = arr(infer(ctx, s), s, t)
    assert infer(ctx, repair) == expected

    em = Emitter()
    for name, term, ty in (
        ('twisted-rule', other_rule, arr(infer(ctx, s), nonzero_start, t)),
        ('untwisted-source', start_to_zero, arr(infer(ctx, s), s, zero_start)),
        ('literal-repair', repair, expected),
    ):
        em.check_type(name, susp_ctx(ctx), susp_tm(term), susp_ty(ty))
    return em


def check_winding():
    # At object a the automorphism law and tensor of morphisms are addition.
    # The positive crossing on a,b has value a*b.
    charges = range(-3, 4)
    for a, b, c in product(charges, repeat=3):
        assert a * (b + c) == a*b + a*c
        assert (a + b) * c == a*c + b*c
    for a, b, opening in product(charges, repeat=3):
        # Close by the inverse of the opening to transport back to the unit.
        crossing = a*b + b*a
        assert opening + crossing - opening == 2*a*b
    # The twist must dominate the two original windings in either order.
    for s, t in product(range(-8, 9), repeat=2):
        exponent = 1 + abs(s - t)
        increase = t - (s + exponent * (1 * -1 + -1 * 1))
        assert increase > 0


def check_cut_counts():
    checks = 0
    for active, length in product(range(4), range(1, 4)):
        columns = [disc_tree(0)] * 4
        columns[active] = string_tree(3, [4] * length)
        ctx = tree_ctx(tuple(columns))
        names = maximal_vars(ctx)
        changes = names[active:active + length]
        sequence = reduce(lambda l, r: comp2(ctx, 4, l, r), map(v, changes))
        slots = (*map(v, names[:active]), sequence, *map(v, names[active + length:]))
        objects = [i for i, ty in enumerate(ctx) if ty == STAR]

        def readings(terms):
            if len(terms) == 1:
                yield terms[0]
            for split in range(1, len(terms)):
                for left in readings(terms[:split]):
                    for right in readings(terms[split:]):
                        yield comp2(ctx, 0, left, right)

        for reading in readings(slots):
            for j in range(4):
                cut = Cut(ctx, objects[j + 1:])
                actual = cut.term(reading)
                assert infer(cut.context(), actual) == cut.type(infer(ctx, reading))
                expected = Counter(cut.indices[i] for i in changes) if j == active else {}
                assert top_counts(cut.context(), actual) == expected
                checks += 1
    return checks


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    check_cube()
    check_winding()
    print(f'{check_cut_counts()} cuts checked on bracketed, whiskered 5-pastes.')
    emitter = check_repair()
    if args.agda_dir:
        name = 'GrayWindingRepairs'
        body = emitter.module(name, __doc__).replace('open import CaTTExp.Pure',
                                                      'open import CaTTExp.Gray.Pure')
        (args.agda_dir / (name + '.agda')).write_text(body)
    print('Checked the signed crossings and the suspended repair at its original faces.')
