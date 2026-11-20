"""Check cap comparisons in the temporal cylinder of a suspended two-arrow path."""
from argparse import ArgumentParser
from pathlib import Path

from catt import (STAR, arr, chain_tree, comp2, disc_tree, glue_tree, infer, maximal_vars,
                  src, sub_from, subst_tm, subst_ty, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident, susp_ctx, susp_tm
from emit_agda import Emitter
from gray_constant_cylinder import whisk
from gray_globe_exterior_actions import certificate, coherence
from gray_penultimate_partial_actions import data, distribute
from gray_temporal_partial_actions import action, rails
from relative_coherence_cut import top_counts


def suspend(operation, value, count):
    for _ in range(count):
        value = operation(value)
    return value


def attach_strip(rank):
    s = rank - 1
    path = tree_ctx(chain_tree(2))
    selected = frozenset(range(len(path)))
    strip, ends, sides = data(path, selected)
    square, arity, _ = action(chain_tree(2), selected)
    assert arity == strip
    old = suspend(susp_ctx, path, s)
    ctx, copies, changes = data(old, frozenset(range(len(old))))
    layers = [list(enumerate(rails(old, ucomp(old), changes, sign)[:s])) for sign in (0, 1)]

    def pad(term, sign):
        for cut, rail in layers[sign]:
            term = whisk(ctx, cut, term, rail, sign)
        return term

    # Recover the lower poles of the common iterated hom from one padded vertex.
    pole_type = infer(ctx, pad(copies[0][2*s], 0))
    pairs = []
    while pole_type != STAR:
        _, pole_type, left, right = pole_type
        pairs.append((left, right))
    assert len(pairs) == s
    labels = [term for pair in reversed(pairs) for term in pair] + [None]*len(strip)
    for i in range(len(path)):
        for sign in (0, 1):
            labels[2*s + ends[sign][i][1]] = pad(copies[sign][2*s + i], sign)
        labels[2*s + sides[i][1]] = changes[2*s + i]
    for i, ty in enumerate(suspend(susp_ctx, strip, s)):
        assert infer(ctx, labels[i]) == subst_ty(ty, labels[:i])
    mixed = subst_tm(suspend(susp_tm, square, s), labels)
    edges = maximal_vars(old)
    assert top_counts(ctx, mixed) == {changes[i][1]: 1 for i in edges}
    return old, ctx, copies, changes, layers, mixed


def comparison(rank, vary_sign):
    s = rank - 1
    old, ctx, copies, changes, layers, mixed = attach_strip(rank)
    edges = maximal_vars(old)
    end_rail = [changes[tgt(old, v(edges[-1]))[1]], changes[src(old, v(edges[0]))[1]]]
    cap_steps = []
    first = last = None
    for sign, layer in enumerate(layers):
        x, y = [copies[sign][i] for i in edges]
        cap = distribute(ctx, s, x, y, layer, sign, bool(sign))
        cap_steps.append(cap)
        if sign == vary_sign:
            # Split the last distributor from all the ones below it.
            cut, rail = layer[-1]
            previous = distribute(ctx, s, x, y, layer[:-1], sign, bool(sign))
            for j, partner in layer[:-1]:
                x, y = (whisk(ctx, j, arg, partner, sign) for arg in (x, y))
            one = distribute(ctx, s, x, y, [(cut, rail)], sign, bool(sign))
            earlier = whisk(ctx, cut, previous, rail, sign)
            first, last = (one, earlier) if sign else (earlier, one)
            assert cap == comp2(ctx, rank, first, last)
            # The last rail is attached to an already padded, compound face.
            end = x
            for _ in range(rank-cut):
                end = (src if sign else tgt)(ctx, end)
            assert end[0] == 'coh' and end == (tgt if sign else src)(ctx, rail)

    # Make two modifications of the two-stage distributor by inserting the
    # identity on its intermediate writing. One uses the left factor's unitor.
    chart = tree_ctx(glue_tree(rank+1, rank, rank+1))
    a, b = map(v, maximal_vars(chart))
    ab = comp2(chart, rank, a, b)
    ax = comp2(chart, rank, a, ident(chart, tgt(chart, a)))
    changed = comp2(chart, rank, ax, b)
    direct = coherence(chart, ab, changed)
    disk = tree_ctx(disc_tree(rank+1))
    f = v(maximal_vars(disk)[0])
    unitor = coherence(disk, f, comp2(disk, rank, f, ident(disk, tgt(disk, f))))
    partial = subst_tm(unitor, sub_from(disk, chart, {f[1]: a}))
    factored = comp2(chart, rank, partial, b)
    cap_comparison = coherence(chart, direct, factored)
    sigma = sub_from(chart, ctx, {a[1]: first, b[1]: last})

    def framed(term):
        sides = cap_steps.copy()
        sides[vary_sign] = term
        minus, plus = [whisk(ctx, s, step, rail, sign)
                       for sign, (step, rail) in enumerate(zip(sides, end_rail))]
        return comp2(ctx, rank, comp2(ctx, rank, minus, mixed), plus)

    begin, end, one, two, filling = [framed(subst_tm(t, sigma))
                                     for t in (ab, changed, direct, factored, cap_comparison)]
    assert begin != end and one != two
    for t in (one, two):
        assert infer(ctx, t) == arr(infer(ctx, begin), begin, end)
    expected = arr(infer(ctx, one), one, two)
    assert infer(ctx, filling) == expected and not top_counts(ctx, filling)
    assert top_counts(ctx, begin) == top_counts(ctx, mixed) == top_counts(ctx, end)
    return ctx, filling, expected


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    for rank in (3, 4):
        for sign in (0, 1):
            ctx, term, ty = comparison(rank, sign)
            if args.agda and (rank, sign) == (3, 0):
                emitter = Emitter()
                certificate(emitter, ctx)('cap-panel-comparison', term, ty)
                args.agda.write_text(emitter.module(args.agda.stem, 'Two rails and two mixed squares.'))
        print(f'Rank {rank}: checked the two mixed squares and both {rank+3}-dimensional comparisons.',
              flush=True)
