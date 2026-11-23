"""Check directed returns across two spatial sites and their local adjunction tests."""
from argparse import ArgumentParser
from collections import deque
from itertools import product
from pathlib import Path

from catt import (STAR, arr, chain_tree, check_ctx, comp2, infer, maximal_vars,
                  src, sub_from, subst_tm, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_scalar_cube import exchange


def prefix_after(c, i, old, new):
    if c <= i:
        return c
    if c <= i + len(old):
        return i + len(new)
    return c - len(old) + len(new)


def extract_partner(path, side):
    # Work in the temporal mirror for the right site.
    initial = 'a' if side == 'L' else 'B'
    word, cut, partner = initial, 1, ''
    cap, cup = [], []
    for state, move in path:
        if not move or move[0] != side:
            continue
        _, index, old, new = move
        complete = state[0]
        if side == 'L':
            i = sum(x.islower() for x in complete[:index])
        else:
            i = sum(x.isupper() for x in complete[index + len(old):])
            old, new = old[::-1], new[::-1]
        assert word[i:i+len(old)] == old
        if cut <= i:
            cup.append((len(partner) + i - cut, old, new))
        else:
            if cut < i + len(old):
                partner += word[cut:i+len(old)]
            cap.append((i, old, new))
        cut = prefix_after(cut, i, old, new)
        word = word[:i] + new + word[i+len(old):]
    assert (cut, word) == (0, initial)

    def rewrite(value, steps):
        for i, old, new in steps:
            assert 0 <= i <= len(value) and value[i:i+len(old)] == old
            value = value[:i] + new + value[i+len(old):]
        return value

    assert rewrite(initial + partner, cap) == ''
    assert rewrite('', cup) == partner + initial


def check_traces(rules, max_width):
    # Two cases use disjoint alphabets; lowercase is the left site.
    start = 'aB'
    parents = {(start, 1, 1): None}
    pending = deque(parents)
    returns = transitions = 0
    while pending:
        word, left, right = pending.popleft()
        if word == 'Ba':
            assert left == 0 or right == 0
            trace = []
            state = (word, left, right)
            while parents[state] is not None:
                state, move = parents[state]
                trace.append((state, move))
            for side, count in [('L', left), ('R', right)]:
                if count == 0:
                    extract_partner(reversed(trace), side)
            returns += 1
        for i in range(len(word) + 1):
            options = []
            if i + 1 < len(word) and word[i].isupper() and word[i + 1].islower():
                options.append((word[i+1] + word[i], 2, left, right, None))
            for side, old, new in rules:
                if not word.startswith(old, i) or len(word) + len(new) - len(old) > max_width:
                    continue
                if side == 'L':
                    p = sum(x.islower() for x in word[:i])
                    l, r = prefix_after(left, p, old, new), right
                else:
                    p = sum(x.isupper() for x in word[i + len(old):])
                    l, r = left, prefix_after(right, p, old[::-1], new[::-1])
                options.append((new, len(old), l, r, (side, i, old, new)))
            for replacement, size, l, r, move in options:
                nxt = word[:i] + replacement + word[i+size:]
                early = [j for j, x in enumerate(nxt) if x.islower()][:l]
                late = [j for j, x in enumerate(nxt) if x.isupper()]
                kept = late[len(late)-r:]
                assert len(early) == l and len(kept) == r
                assert not early or not kept or early[-1] < kept[0]
                transitions += 1
                state = (nxt, l, r)
                if state not in parents:
                    parents[state] = ((word, left, right), move)
                    pending.append(state)
    return transitions, returns


def typed_return(em, dual):
    # Reflect both the spatial and temporal orders for the other adjunction.
    # The dimension-three arrows still run forwards, including native exchange.
    ctx = (STAR,) * 3
    left = arr(STAR, v(0), v(1))
    right = arr(STAR, v(1), v(2))
    ctx += (left, left, right, right)
    f, h, g, j = map(v, (3, 4, 5, 6) if not dual else (6, 5, 4, 3))
    first, last = (tgt, src) if dual else (src, tgt)

    def join(c, cut, x, y):
        return comp2(c, cut, y, x) if dual else comp2(c, cut, x, y)

    def arrow(x, y):
        return arr(infer(ctx, x), y, x) if dual else arr(infer(ctx, x), x, y)

    a, d, b = map(v, range(len(ctx), len(ctx) + 3))
    ctx += (arrow(f, h), arrow(h, f), arrow(g, j))
    unit, counit = v(len(ctx)), v(len(ctx) + 1)
    unit_source, counit_target = identity(ctx, h), identity(ctx, f)
    ctx += (arr(infer(ctx, unit_source), unit_source, join(ctx, 1, d, a)),
            arr(infer(ctx, counit_target), join(ctx, 1, a, d), counit_target))
    check_ctx(ctx)

    def fit(template, actual, endpoints):
        # The template has either one moving spatial column, or one temporal string.
        arity = tree_ctx(template)
        slots = maximal_vars(arity)
        sigma = sub_from(arity, ctx, dict(zip(slots, actual)))
        s, t = endpoints(arity, list(map(v, slots)))
        return subst_tm(head(arity, s, t), sigma)

    def whisk(x, y):
        return join(ctx, 0, x, y)

    def then(x, y):
        return join(ctx, 1, x, y)

    def spatial_fit(items, edge, endpoints):
        cols = [chain_tree(len(items)), ()]
        labels = [*items, edge]
        if dual:
            cols.reverse()
            labels.reverse()
        def bound(c, vs):
            vs = vs[::-1] if dual else vs
            return endpoints(c, vs[:-1], vs[-1])
        return fit(tuple(cols), labels, bound)

    def combine(cells):
        answer = cells[0]
        for cell in cells[1:]:
            answer = comp2(ctx, 2, answer, cell)
        return answer

    def temporal_fit(events, left_shape, right_shape):
        def read(c, shape, vs):
            if isinstance(shape, int):
                return vs[shape]
            return join(c, 1, read(c, shape[0], vs), read(c, shape[1], vs))
        return fit(string_tree(1, [2]*len(events)), events[::-1] if dual else events,
                   lambda c, vs: (read(c, left_shape, vs[::-1] if dual else vs),
                                  read(c, right_shape, vs[::-1] if dual else vs)))

    def fit_unit(history, pole, edge, insert):
        ty = tree_ctx(string_tree(1, [2]))
        slot, = maximal_vars(ty)
        t = v(slot)
        if insert:
            padded = join(ty, 1, t, identity(ty, last(ty, t)))
            disc_fit = head(ty, t, padded)
        else:
            padded = join(ty, 1, identity(ty, first(ty, t)), t)
            disc_fit = head(ty, padded, t)
        disc_fit = subst_tm(disc_fit, sub_from(ty, ctx, {slot: history}))
        cols = ((), ())
        def ends(c, vs):
            x, y = vs[::-1] if dual else vs
            exact = identity(c, join(c, 0, x, y))
            padded = join(c, 0, identity(c, x), y)
            return (exact, padded) if insert else (padded, exact)
        labels = [edge, pole] if dual else [pole, edge]
        local = fit(cols, labels, ends)
        return (combine([disc_fit, then(history, local)]) if insert else
                combine([then(local, history), disc_fit]))

    def distribute(items, edge, expand):
        def ends(c, xs, y):
            u, w = xs
            whole = join(c, 0, join(c, 1, u, w), y)
            parts = join(c, 1, join(c, 0, u, y), join(c, 0, w, y))
            return (whole, parts) if expand else (parts, whole)
        return spatial_fit(items, edge, ends)

    original = exchange(ctx, b, a) if dual else exchange(ctx, a, b)
    old, final = tgt(ctx, original), src(ctx, original)
    before, after = fit_unit(old, h, j, True), fit_unit(final, f, g, False)
    first_fit = combine([then(old, distribute([d, a], j, True)),
                         temporal_fit([whisk(a, g), whisk(h, b), whisk(d, j), whisk(a, j)],
                                      ((0, 1), (2, 3)), ((0, (1, 2)), 3))])
    second_fit = combine([temporal_fit([whisk(a, g), whisk(d, g), whisk(f, b), whisk(a, j)],
                                       ((0, (1, 2)), 3), ((0, 1), (2, 3))),
                          then(distribute([a, d], g, False), final)])
    insertion = join(ctx, 1, old, join(ctx, 0, unit, j))
    cancellation = join(ctx, 1, join(ctx, 0, counit, g), final)
    crossing = exchange(ctx, b, d) if dual else exchange(ctx, d, b)
    carried = join(ctx, 1, join(ctx, 1, join(ctx, 0, a, g), crossing), join(ctx, 0, a, j))
    steps = [before, insertion, first_fit, carried, second_fit, cancellation, after]
    proof = steps[0]
    for step in steps[1:]:
        assert tgt(ctx, proof) == src(ctx, step)
        proof = comp2(ctx, 2, proof, step)
    ty = arr(infer(ctx, old), tgt(ctx, original), src(ctx, original))
    em.check_type('rightSite' if dual else 'leftSite', ctx, proof, ty)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    total = successes = configurations = 0
    pairs = [('', 'ca'), ('ac', ''), ('', 'ac'), ('ca', '')]
    for flags in product((False, True), repeat=8):
        rules = [('L', u, w) for k, (u, w) in enumerate(pairs) if flags[k]]
        rules += [('R', u.upper().replace('A', 'B'), w.upper().replace('A', 'B'))
                  for k, (u, w) in enumerate(pairs) if flags[4+k]]
        steps, ends = check_traces(rules, 4)
        expected = (flags[0] and flags[1]) or (flags[6] and flags[7])
        assert bool(ends) == expected
        total += steps
        successes += bool(ends)
        configurations += ends
    print('Mixed transitions, returning systems, marked returns:', total, successes, configurations)
    em = Emitter()
    for dual in (False, True):
        typed_return(em, dual)
    if args.agda_dir:
        name = 'GrayAdjointExchange'
        module = em.module(name, __doc__).replace('open import CaTTExp.Pure\n',
                                                   'open import CaTTExp.Gray.Pure\n')
        (args.agda_dir / (name + '.agda')).write_text(module)
