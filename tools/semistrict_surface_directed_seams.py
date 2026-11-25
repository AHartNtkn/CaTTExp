"""Check directed degree-six transport across a moving endpoint and a shared four-face."""
from argparse import ArgumentParser
from collections import Counter
from functools import reduce
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, chain_tree, comp2, disc_tree, glue_tree, infer,
                  maximal_vars, src, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head
from semistrict_surface_equal_rank import suspend
from semistrict_surface_exact_boundary import accepted, run
from semistrict_surface_grid_tracks import temporal
from semistrict_surface_insertion_cut import Assertions
from semistrict_surface_insertion_tracks import insert
from semistrict_surface_nested_carriers import apply
from semistrict_surface_rank_cut import RankCut


def paste(ctx, cells):
    return reduce(lambda x, y: temporal(ctx, x, y), cells)


def adjust(ctx, cells, start, end):
    """Compare two bracketings on their free temporal row before applying the labels."""
    row = tree_ctx(suspend(chain_tree(len(cells)), 4))
    variables = list(map(v, maximal_vars(row)))
    comparison = head(row, start(row, variables), end(row, variables))
    return apply(row, comparison, ctx, cells)


def replace(ctx, prefix, before, after, suffix, cell):
    """Use a directed comparison once at a consecutive subword of five-cells."""
    assert src(ctx, cell) == paste(ctx, before) and tgt(ctx, cell) == paste(ctx, after)

    def group(p, terms):
        left = len(prefix)
        right = len(terms) - len(suffix)
        result = paste(p, terms[left:right])
        if prefix:
            result = temporal(p, paste(p, terms[:left]), result)
        if suffix:
            result = temporal(p, result, paste(p, terms[right:]))
        return result

    fit = cell
    if prefix:
        fit = comp2(ctx, 4, paste(ctx, prefix), fit)
    if suffix:
        fit = comp2(ctx, 4, fit, paste(ctx, suffix))
    first = adjust(ctx, prefix + before + suffix, paste, group)
    last = adjust(ctx, prefix + after + suffix, group, paste)
    return paste(ctx, [first, fit, last])


def cap(ctx, term, reverse=False):
    disc = tree_ctx(disc_tree(4))
    x = v(maximal_vars(disc)[0])
    padded = temporal(disc, x, ident(disc, tgt(disc, x)))
    move = head(disc, x, padded) if reverse else head(disc, padded, x)
    return apply(disc, move, ctx, [term])


def chart(count):
    # A vertical string of five-cells, beside a four-arrow at cut three.
    column = chain_tree(count)
    row = tree_ctx(suspend(column, 4))
    extended = tree_ctx(suspend((column, ()), 3))
    return row, extended


def generic(count):
    row, extended = chart(count)
    changes = list(map(v, maximal_vars(row)))
    x = src(row, changes[0])
    y = tgt(row, changes[-1])
    nonstandard = head(row, src(row, cap(row, x)), y)
    # At the new labels undo the change of the source, then evaluate the same head.
    new = head(row, paste(row, changes), temporal(row, cap(row, x, True), nonstandard))
    *old_labels, k = map(v, maximal_vars(extended))
    assert len(old_labels) == count
    lifted = apply(row, nonstandard, extended, old_labels)
    old_cap = cap(extended, src(extended, old_labels[0]))
    carried = [comp2(extended, 3, f, k) for f in [old_cap, *old_labels]]
    old = head(extended, comp2(extended, 3, lifted, k), paste(extended, carried))
    return row, extended, nonstandard, old, new


def check(binary, folder, count):
    ctx = (STAR,)

    def declare(ty):
        nonlocal ctx
        var = v(len(ctx))
        ctx += (ty,)
        return var

    base = v(0)
    for _ in range(2):
        base = declare(arr(infer(ctx, base), base, base))
    pole = arr(infer(ctx, base), base, base)
    a, b, c = [declare(pole) for _ in range(3)]
    k = declare(arr(pole, b, c))
    old = [declare(arr(pole, a, b)) for _ in range(count + 1)]
    new = [declare(arr(pole, a, c)) for _ in range(count + 1)]

    def arrow(x, y):
        assert infer(ctx, x) == infer(ctx, y)
        return declare(arr(infer(ctx, x), x, y))

    alpha = [arrow(x, y) for x, y in zip(old, old[1:])]
    beta = [arrow(x, y) for x, y in zip(new, new[1:])]
    squares = [arrow(temporal(ctx, x, k), y) for x, y in zip(old, new, strict=True)]
    carried = [comp2(ctx, 3, f, k) for f in alpha]
    gates = [arrow(temporal(ctx, f, following), temporal(ctx, preceding, g))
             for f, following, preceding, g in zip(carried, squares[1:], squares[:-1], beta, strict=True)]

    row, extended, operation, old_generic, new_generic = generic(count)
    old_head = apply(row, operation, ctx, alpha)
    new_head = apply(row, operation, ctx, beta)
    old_cap = comp2(ctx, 3, cap(ctx, old[0]), k)
    new_cap = cap(ctx, new[0], True)
    start = comp2(ctx, 3, old_head, k)
    steps = [replace(ctx, [], [start], [old_cap, *carried], [squares[-1]],
                     apply(extended, old_generic, ctx, [*alpha, k]))]
    for i in reversed(range(count)):
        steps.append(replace(ctx, [old_cap, *carried[:i]], [carried[i], squares[i+1]],
                             [squares[i], beta[i]], beta[i+1:], gates[i]))
    steps.append(replace(ctx, [old_cap, squares[0]], beta, [new_cap, new_head], [],
                         apply(row, new_generic, ctx, beta)))
    proof = paste(ctx, steps)
    left = temporal(ctx, start, squares[-1])
    right = temporal(ctx, paste(ctx, [old_cap, squares[0], new_cap]), new_head)
    raw = RankCut(0, binary, folder)
    assert raw.checks(ctx, proof, arr(infer(ctx, left), left, right))
    assert not raw.checks(ctx, proof, arr(infer(ctx, left), right, left))
    assert top_counts(ctx, proof) == Counter(z[1] for z in gates)
    for i, bcell in enumerate(beta):
        j = bcell[1]
        assert top_counts(ctx, right)[j] - top_counts(ctx, left)[j] == 1
        for k_index, gate in enumerate(gates):
            change = top_counts(ctx, tgt(ctx, gate))[j] - top_counts(ctx, src(ctx, gate))[j]
            assert change == int(i == k_index)

    writer = Assertions()
    declarations = []
    for i, ty in enumerate(ctx):
        written = '*' if ty == STAR else f'{writer.term(ty[2])} -> {writer.term(ty[3])}'
        declarations.append(f'(x{i} : {written})')
    lterm, rterm, witness = (writer.term(term) for term in (left, right, proof))
    query = f'def transport {" ".join(declarations)} : {lterm} -> {rterm} = {witness}'
    name = 'DirectedSeam.catt'
    (folder / name).write_text('\n'.join([*writer.commands, query]) + '\n')
    accepted(run(binary, folder, name), name, ['transport'])
    print(f'{count} directed input cubes: weak checker accepted transport at the written faces.')


def check_converted_head(binary, folder):
    pair = glue_tree(3, 0, 3)
    joined, _, _, change = insert(ucomp(tree_ctx(pair)), pair, (0,), pair)
    base = tree_ctx(joined)
    g, h = src(base, change), tgt(base, change)
    arrows = tree_ctx((disc_tree(3),) * 3)
    top = list(map(v, maximal_vars(arrows)))

    def carrier(reading):
        start = apply(base, reading, arrows, [src(arrows, f) for f in top])
        end = apply(base, g, arrows, [tgt(arrows, f) for f in top])
        return head(arrows, start, end)

    bigons = tree_ctx((disc_tree(4),) * 3)
    slots = list(map(v, maximal_vars(bigons)))
    low = apply(arrows, carrier(g), bigons, [src(bigons, f) for f in slots])
    same = apply(arrows, carrier(g), bigons, [tgt(bigons, f) for f in slots])
    different = apply(arrows, carrier(h), bigons, [tgt(bigons, f) for f in slots])
    repaired = head(bigons, low, same)
    ty = arr(infer(bigons, low), low, different)
    converted = ('coh', bigons, ty, tuple(map(v, range(len(bigons)))))
    low_rank = RankCut(2, binary, folder)
    high_rank = RankCut(3, binary, folder)
    assert high_rank.checks(bigons, converted, ty)
    assert not low_rank.equal_type(bigons, infer(bigons, low), infer(bigons, different))
    assert low_rank.checks(bigons, repaired, infer(bigons, repaired))
    assert high_rank.equal_term(bigons, converted, repaired)
    print('Converted five-head: forms at cap three, faces disagree at cap two, '
          'repaired head checks at cap two with the same cap-three value.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('binary', type=Path)
    args = parser.parse_args()
    with TemporaryDirectory() as scratch:
        for n in (2, 3):
            check(args.binary.resolve(), Path(scratch), n)
        check_converted_head(args.binary.resolve(), Path(scratch))
