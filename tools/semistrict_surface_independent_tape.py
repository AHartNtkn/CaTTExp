"""Check the independent tape at a prescribed old boundary in both kernels."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import arr, check_ctx, comp2, disc_tree, infer, subst_tm, subst_ty, tgt, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_first_failure_gate import compare_on_disc, unchanged


def boundary_checks(em, k):
    m = k - 2
    disc = tree_ctx(disc_tree(k))
    old_move = v(len(disc) - 1)
    _, _, u, other = disc[-1]
    b = tgt(disc, u)
    ctx = disc
    erase = tuple(v(i) for i in range(len(disc)))

    def declare(ty, image):
        nonlocal ctx, erase
        assert infer(disc, image) == subst_ty(ty, erase)
        result = v(len(ctx))
        ctx += (ty,)
        erase += (image,)
        return result

    h = declare(infer(disc, b), b)
    idle = identity(disc, b)
    opening = declare(arr(infer(ctx, b), b, h), idle)
    closing = declare(arr(infer(ctx, b), h, b), idle)
    letter = arr(infer(ctx, h), h, h)
    a, c, d = [declare(letter, idle) for _ in range(3)]

    def double_idle(gamma, p):
        unit = identity(gamma, p)
        return comp2(gamma, m, unit, unit)

    move = declare(arr(letter, comp2(ctx, m, a, c), d),
                   compare_on_disc(disc, b, double_idle, identity))
    check_ctx(ctx)

    def tape(gamma, op, word, cl):
        return comp2(gamma, m, comp2(gamma, m, op, word), cl)

    first = tape(ctx, opening, comp2(ctx, m, a, c), closing)
    last = tape(ctx, opening, d, closing)
    start = comp2(ctx, m, u, first)
    end = comp2(ctx, m, other, last)
    literal = comp2(ctx, k - 1, comp2(ctx, m, old_move, first),
                    comp2(ctx, m, other, tape(ctx, opening, move, closing)))
    ty = arr(infer(ctx, start), start, end)
    em.check_type(f'carry{k}', ctx, literal, ty)

    def padded(gamma, t, long):
        unit = identity(gamma, tgt(gamma, t))
        word = comp2(gamma, m, unit, unit) if long else unit
        return comp2(gamma, m, t, tape(gamma, unit, word, unit))

    enter = compare_on_disc(disc, u, unchanged, lambda g, t: padded(g, t, True))
    leave = compare_on_disc(disc, other, lambda g, t: padded(g, t, False), unchanged)
    returned = comp2(disc, k - 1, comp2(disc, k - 1, enter, subst_tm(literal, erase)), leave)
    em.check_type(f'retract{k}', disc, returned, disc[-1])


def check_interchange():
    # Enumerate typed temporal paths in the projected computad. A lower product
    # places its arguments on disjoint wires; all their shuffles serialize it.
    def paths(width, bound):
        yield '', width
        if bound:
            for symbol in 'o' + ('cab' if width else ''):
                new = width + (symbol == 'o') - (symbol == 'c')
                for suffix, final in paths(new, bound - 1):
                    yield symbol + suffix, final

    def shuffles(s, t):
        if not s or not t:
            return {s + t}
        return ({s[0] + w for w in shuffles(s[1:], t)} |
                {t[0] + w for w in shuffles(s, t[1:])})

    checked = 0
    for widths in product(range(2), repeat=2):
        for (s, _), (t, _) in product(*(paths(n, 4) for n in widths)):
            if sum(widths) + (s + t).count('o') <= 1:
                assert shuffles(s, t) == {s + t}
                checked += 1
    return checked


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    print('Bounded-load pairs of paths:', check_interchange())
    em = Emitter()
    for degree in (3, 4, 5):
        boundary_checks(em, degree)
    if args.agda_dir:
        for prefix, kernel in [('Ordinary', 'CaTTExp.Pure'), ('Gray', 'CaTTExp.Gray.Pure')]:
            name = prefix + 'IndependentTape'
            module = em.module(name, __doc__).replace('open import CaTTExp.Pure\n',
                                                       f'open import {kernel}\n')
            (args.agda_dir / (name + '.agda')).write_text(module)
