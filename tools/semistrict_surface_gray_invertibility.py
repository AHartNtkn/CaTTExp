"""Check the local dimension bound and directed top support on folded Gray cells."""
from argparse import ArgumentParser
from functools import cache
from itertools import product
from pathlib import Path

from catt import STAR, arr, comp2, disc_tree, infer, maximal_vars, src, tdim_tm, tgt, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head
from semistrict_surface_scalar_cube import exchange


@cache
def multiplicity(ctx, term):
    return sum(top_counts(ctx, term).values())


def weights(ctx):
    result = [0, 1]
    names = [v(i) for i in range(len(ctx))]
    for rank in range(2, 1 + max(tdim_tm(ctx, g) for g in names)):
        growth = max((multiplicity(ctx, tgt(ctx, g)) - multiplicity(ctx, src(ctx, g))
                      for g in names if tdim_tm(ctx, g) == rank), default=0)
        result.append(max(rank-1, result[-1]*growth))
    return tuple(result)


def budget(ctx, term, costs):
    value = 0
    for rank in reversed(range(1, tdim_tm(ctx, term)+1)):
        value += costs[rank]*multiplicity(ctx, term)
        term = src(ctx, term)
    return value


def mixed_context():
    loop = arr(STAR, v(0), v(0))
    ctx = (STAR, loop)
    f = v(1)
    empty = ident(ctx, v(0))
    ff = comp2(ctx, 0, f, f)
    ctx += (arr(loop, empty, ff), arr(loop, ff, empty), arr(loop, f, f))
    a = v(4)
    triple = comp2(ctx, 1, a, comp2(ctx, 1, a, a))
    ctx += (arr(infer(ctx, a), a, triple), arr(infer(ctx, a), a, a))
    t = v(6)
    ctx += (arr(infer(ctx, t), t, comp2(ctx, 2, t, comp2(ctx, 2, t, t))),)
    return ctx


def check_budgets():
    ctx = mixed_context()
    costs = weights(ctx)
    assert costs == (0, 1, 2, 4, 8)
    count = 0
    for length in range(1, 4):
        for names in product(range(1, len(ctx)), repeat=length):
            # Under the tensor-to-cartesian projection the atom is a padded
            # ordinary horizontal composite; padding leaves its budget fixed.
            cell = v(names[0])
            for name in names[1:]:
                cell = comp2(ctx, 0, cell, v(name))
            size = budget(ctx, cell, costs)
            assert size == sum(budget(ctx, v(i), costs) for i in names)
            assert size >= sum(tdim_tm(ctx, v(i))-1 for i in names)
            for side in (src, tgt):
                face = cell
                while tdim_tm(ctx, face):
                    face = side(ctx, face)
                    assert budget(ctx, face, costs) <= size
            count += 1
    # Sharp with arbitrarily many copies of a scalar and zero-length spatial poles.
    base = (STAR,)
    unit = ident(base, v(0))
    scalar_ctx = (*base, arr(infer(base, unit), unit, unit))
    a = v(1)
    for length in range(1, 14):
        assert budget(scalar_ctx, a, weights(scalar_ctx)) == length
        a = comp2(scalar_ctx, 0, a, v(1))
    return count


def cancellation_chain(depth):
    base = (STAR,)
    unit = ident(base, v(0))
    ctx = (*base, arr(infer(base, unit), unit, unit))
    current = exchange(ctx, v(1), v(1))
    cells = []
    for level in range(depth+1):
        source, target = src(ctx, current), tgt(ctx, current)
        ctx += (arr(infer(ctx, source), target, source),)
        reverse = v(len(ctx)-1)
        round_trip = comp2(ctx, tdim_tm(ctx, current)-1, current, reverse)
        cells.append((current, reverse, round_trip))
        if level < depth:
            ctx += (arr(infer(ctx, round_trip), round_trip, ident(ctx, source)),)
            current = v(len(ctx)-1)
    # The final composite has a fresh top generator. Any further cancellation
    # would need to identify its positive ordinary count with the count zero.
    assert multiplicity(ctx, round_trip) >= 1
    return ctx, cells


def examples():
    out = Emitter()
    out.checks.append('occupied : TSet → Bool\noccupied [] = false\noccupied (_ ∷ _) = true\n')
    def verify(name, ctx, term, nonidentity):
        out.check_typed(name, ctx, term)
        out.checks.append(f'{name}-support : occupied (topS {out.tm(term)}) ≡ '
                          f'{"true" if nonidentity else "false"}\n{name}-support = refl\n')
    base = (STAR,)
    unit = ident(base, v(0))
    ctx = (*base, arr(infer(base, unit), unit, unit))
    a = v(1)
    square = exchange(ctx, a, a)
    p, q = src(ctx, square), tgt(ctx, square)
    ctx += (arr(infer(ctx, p), q, p),)
    verify('folded-square', ctx, square, True)
    verify('directed-return', ctx, v(2), True)
    verify('round-trip', ctx, comp2(ctx, 2, square, v(2)), True)
    verify('padded-round-trip', ctx, ident(ctx, comp2(ctx, 2, square, v(2))), False)
    verify('squared-input', ctx, exchange(ctx, comp2(ctx, 1, a, a), a), True)
    for stationary in (0, 1):
        ranks = [1, 1]
        ranks[stationary] = 0
        arity = tree_ctx(tuple(disc_tree(h) for h in ranks))
        labels = list(map(v, maximal_vars(arity)))
        labels[stationary] = ident(arity, labels[stationary])
        forward = exchange(arity, *labels)
        s, t = src(arity, forward), tgt(arity, forward)
        backward = head(arity, t, s)
        verify(f'thin-{stationary}', arity, forward, False)
        verify(f'inverse-{stationary}', arity, backward, False)
        for i, (fst, snd, face) in enumerate(((forward, backward, s), (backward, forward, t))):
            composite = comp2(arity, 2, fst, snd)
            verify(f'cancel-{stationary}-{i}', arity, head(arity, composite, ident(arity, face)), False)
    chain_ctx, chain = cancellation_chain(3)
    for level, triple in enumerate(chain):
        for kind, term in zip(('forward', 'reverse', 'round-trip'), triple):
            verify(f'chain-{level}-{kind}', chain_ctx, term, True)
    return out


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    print(f'{check_budgets()} projected generator words and their iterated faces checked.')
    emitter = examples()
    if args.agda_dir:
        name = 'GrayInvertibility'
        module = emitter.module(name, __doc__).replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure')
        (args.agda_dir / (name + '.agda')).write_text(module)
    print('25 typing and top-support judgments, including a cancellation chain through rank six.')
