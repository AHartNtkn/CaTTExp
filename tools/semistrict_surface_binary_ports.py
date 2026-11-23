"""Check bounded-port compilation with a nested unbiased input and an empty output."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, comp_tree, glue_tree, infer, maximal_vars, src,
                  sub_from, subst_tm, subst_ty, tdim_tm, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity


def check_compilation(em, n):
    # Work inside a single hom even for the two moving adjacent slots.
    j = n - 2
    ctx = (STAR,)
    pole = v(0)
    for _ in range(j):
        pole_type = arr(infer(ctx, pole), pole, pole)
        pole = v(len(ctx))
        ctx += (pole_type,)
    arrow = arr(infer(ctx, pole), pole, pole)
    f, g = v(len(ctx)), v(len(ctx) + 1)
    ctx += (arrow, arrow)
    a, b = v(len(ctx)), v(len(ctx) + 1)
    ctx += (arr(arrow, f, f), arr(arrow, g, g))

    line = ((), (), ())
    for _ in range(n - 1):
        line = (line,)
    line_ctx = tree_ctx(line)
    l, m, r = [v(i) for i in maximal_vars(line_ctx)]
    biased = comp2(line_ctx, n - 1, comp2(line_ctx, n - 1, l, m), r)
    unbiased = comp_tree(line, line_ctx, [l, m, r])
    repeat = sub_from(line_ctx, ctx, {i: a for i in maximal_vars(line_ctx)})
    triple = subst_tm(unbiased, repeat)
    reassoc = subst_tm(head(line_ctx, unbiased, biased), repeat)
    reassoc_back = subst_tm(head(line_ctx, biased, unbiased), repeat)
    source = comp2(ctx, j, triple, b)
    target = identity(ctx, tgt(ctx, source))
    z_type = arr(infer(ctx, source), source, target)
    old = ctx + (z_type,)
    z = v(len(ctx))
    fold = tuple(v(i) for i in range(len(ctx)))
    profiles = []

    def occurrences(term):
        if term[0] == 'v':
            return int(tdim_tm(ctx, term) == n)
        return sum(occurrences(arg) for arg in term[3])

    def declare(ty, image):
        nonlocal ctx, fold
        assert infer(old, image) == subst_ty(ty, fold)
        slot = v(len(ctx))
        ctx += (ty,)
        fold += (image,)
        return slot

    def gate(s, t, image):
        ports = (occurrences(s), occurrences(t))
        assert ports in ((2, 1), (1, 1), (1, 0))
        profiles.append(ports)
        return declare(arr(infer(ctx, s), s, t), image)

    def compose(steps):
        result = steps[0]
        for step in steps[1:]:
            result = comp2(ctx, n, result, step)
        return result

    pair = comp2(ctx, n - 1, a, a)
    x = declare(infer(ctx, pair), pair)
    take_pair = gate(pair, x, identity(old, pair))
    y = declare(infer(ctx, triple), triple)
    take_third = gate(comp2(ctx, n - 1, x, a), y, reassoc_back)
    fit = compose([reassoc, comp2(ctx, n - 1, take_pair, a), take_third])
    fit_outer = comp2(ctx, j, fit, b)

    chart = tree_ctx(glue_tree(n, j, n))
    slots = maximal_vars(chart)
    p, q = [v(i) for i in slots]
    both = comp2(chart, j, p, q)
    left = comp2(chart, j, p, src(chart, q))
    right = comp2(chart, j, tgt(chart, p), q)
    serial = comp2(chart, n - 1, left, right)
    sigma = sub_from(chart, ctx, dict(zip(slots, (y, b))))
    forward = subst_tm(head(chart, both, serial), sigma)
    backward = subst_tm(head(chart, serial, both), sigma)
    left, right = (subst_tm(t, sigma) for t in (left, right))
    reads = []
    moves = []
    for piece in (left, right):
        old_piece = subst_tm(piece, fold)
        label = declare(infer(ctx, piece), old_piece)
        reads.append(label)
        moves.append(gate(piece, label, identity(old, old_piece)))
    out = declare(infer(ctx, source), source)
    take_both = gate(comp2(ctx, n - 1, *reads), out, subst_tm(backward, fold))
    empty = declare(infer(ctx, target), target)
    centre = gate(out, empty, z)
    expand = gate(empty, target, identity(old, target))
    translated = compose([fit_outer, forward, comp2(ctx, n - 1, moves[0], right),
                          comp2(ctx, n - 1, reads[0], moves[1]), take_both, centre, expand])
    check_ctx(ctx)
    em.check_type(f'compiled{n+1}', ctx, translated, z_type)
    em.check_type(f'returned{n+1}', old, subst_tm(translated, fold), z_type)
    return profiles


def check_wire_balance():
    """Compare the component criterion with token balance at every named wire."""
    profiles = [(0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (0, 0)]
    checks = 0
    for gates in product(profiles, repeat=3):
        # Begin with just enough wires for this order; prioritize fresh outputs.
        balance = needed = 0
        for take, give in gates:
            needed = max(needed, take - balance)
            balance += give - take
        live = [(-1, i) for i in range(needed)]
        wires = []
        for step, (take, give) in enumerate(gates):
            wires.extend((site, step) for site in live[:take])
            live = [(step, i) for i in range(give)] + live[take:]
        wires.extend((site, -1) for site in live)
        # The extra vertex denotes the two external boundaries with multiplicity one.
        components = [{i} for i in range(-1, len(gates))]
        for (source, _), target in wires:
            left = next(c for c in components if source in c)
            right = next(c for c in components if target in c)
            if left != right:
                left.update(right)
                components.remove(right)
        for uses in product(range(3), repeat=len(gates)):
            counts = {**dict(enumerate(uses)), -1: 1}
            consistent = all(len({counts[i] for i in c}) == 1 for c in components)
            balanced = all((source == -1) + (uses[source] if source >= 0 else 0)
                           - (uses[target] if target >= 0 else 0) == (target == -1)
                           for (source, _), target in wires)
            assert consistent == balanced
            checks += 1
    return checks


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    print('Wire-balance assignments:', check_wire_balance())
    em = Emitter()
    for n in (3, 4):
        print('Degree, directed gate ports:', n + 1, check_compilation(em, n))
    if args.agda_dir:
        for prefix, kernel in [('Ordinary', 'CaTTExp.Pure'), ('Gray', 'CaTTExp.Gray.Pure')]:
            name = prefix + 'BinaryPorts'
            module = em.module(name, __doc__).replace('open import CaTTExp.Pure\n',
                                                       f'open import {kernel}\n')
            (args.agda_dir / (name + '.agda')).write_text(module)
