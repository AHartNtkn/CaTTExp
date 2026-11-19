"""Check the corner bridges with both pure 2-variables allowed to change."""
import argparse
from collections import Counter
from functools import cache
from itertools import permutations
from pathlib import Path

from canonical_gray_two_discs import strict_interpreter
from catt import comp2, fv_tm, infer, maximal_vars, src, tgt, tree_ctx
from emit_agda import Emitter
from gray_globe_attachments import ordered_factors
from gray_globe_comparison import atom, face
from gray_globe_exterior_actions import arity, certificate
from gray_globe_factorizations import profile, rank
from gray_globe_pure_extension import extend, raise_argument, two_by_two
from gray_globe_section import EMPTY_ROW, cells
from gray_globe_sector_terms import arrow, boundary_bridge
from gray_globe_strip_gluing import factors
from gray_globe_strip_squares import chart_lift, lift_on


def fold(ctx, cut, terms):
    t, *rest = terms
    for u in rest:
        t = comp2(ctx, cut, t, u)
    return t


def leaves(t):
    if t[0] == 'coh' and t[1] == arity(1, (2, 2)):
        return sum((leaves(t[3][j]) for j in maximal_vars(t[1])), ())
    return (t,)


def cube(ctx, edge, square, compare):
    """Paste the six faces between the same two bracketed three-edge paths."""
    @cache
    def word(order):
        state = 0
        terms = []
        for d in order:
            terms.append(edge(state, d))
            state |= 1 << d
        return tuple(terms)

    def swap(order, i):
        state = 0 if i == 0 else 1 << order[0]
        s = square(state, order[i], order[i+1])
        args = word(order)
        other = order[:i] + (order[i+1], order[i]) + order[i+2:]
        args2 = word(other)
        if i == 0:
            t = comp2(ctx, 2, s, args[2])
        else:
            t = comp2(ctx, 2, args[0], s)
            before = chart_lift(ctx, args, 2, fold(ctx, 2, args), src(ctx, t))
            after = chart_lift(ctx, args2, 2, tgt(ctx, t), fold(ctx, 2, args2))
            t = fold(ctx, 3, (before, t, after))
        assert infer(ctx, t) == arrow(ctx, fold(ctx, 2, args), fold(ctx, 2, args2))
        return other, t

    def path(indices):
        order = (0, 1, 2)
        steps = []
        for i in indices:
            order, t = swap(order, i)
            steps.append(t)
        assert order == (2, 1, 0)
        return fold(ctx, 3, steps)

    return compare(path((0, 1, 0)), path((1, 0, 1)))


def check(data, emitter):
    ctx, names, chosen = data
    evaluate = strict_interpreter(ctx, tuple(names))
    certify = certificate(emitter, ctx) if emitter else None
    certified = set()
    counts = Counter()
    for p in sorted(chosen):
        if len(p) != 4 or len(p[2][0]) != 3 or {rank(g) for g in p[3][0]} != {(0, 3), (3, 0)}:
            continue
        high = tuple(names[g] for g in p[3][0])

        def activate(t, d):
            return raise_argument(ctx, t, src(ctx, high[d]), high[d])

        def state_term(t, mask):
            for d in (0, 1):
                if mask & (1 << d):
                    t = tgt(ctx, activate(t, d))
            return t

        # The third coordinate passes from the native to the other cut-one split.
        base = face(p, 0)
        holes = ((1, 2), (2, 1))
        starts = [fold(ctx, 1, [chosen[s] for s in factors(base, h)]) for h in holes]
        assert starts[0] == chosen[base]
        modes = [leaves(t) for t in starts]
        assert all(len(ws) == 3 for ws in modes)
        chain = modes[0] == modes[1]
        fixed, = (t for t in modes[0] if t[0] == 'v')
        pure_first = modes[0][-1] == fixed
        def inside(ws):
            return ws[:2] if pure_first else ws[1:]

        def whisk(t):
            return comp2(ctx, 1, t, fixed) if pure_first else comp2(ctx, 1, fixed, t)

        def frame(parts, mask, done):
            # Replace slots for completed pure moves by their targets.
            args = []
            for t in parts:
                if t[0] == 'v' and t == fixed:
                    args.append(t)
                    continue
                d, = (i for i, g in enumerate(high) if src(ctx, g)[1] in fv_tm(t))
                if done & (1 << d):
                    args.append(tgt(ctx, activate(t, d)))
                elif mask & (1 << d):
                    args.append(activate(t, d))
                else:
                    args.append(t)
            return args

        @cache
        def spatial(mode, s, t):
            return chart_lift(ctx, [chosen[q] for q in factors(p, holes[mode])], 1, s, t)

        def finish(w, kind):
            assert evaluate(w) == p + (EMPTY_ROW,) * 2
            counts[kind] += 1
            if certify and kind not in certified:
                certify(kind, w, infer(ctx, w))
                certified.add(kind)

        def use_chart(vertices, single, link, top, boundary_xy):
            # All fields are indexed by the two pure bits and by the cut choice.
            @cache
            def edge(state, d):
                z, mode = state & 3, state >> 2
                if d == 2:
                    return link(z)
                return single(mode, z, d)

            @cache
            def sq(state, d, e):
                assert d < e
                a = comp2(ctx, 2, edge(state, d), edge(state | (1 << d), e))
                b = comp2(ctx, 2, edge(state, e), edge(state | (1 << e), d))
                if e == 1:
                    return boundary_xy(state >> 2, a, b)
                return top(1 << d, state & 3, a, b)

            for order in permutations(range(3)):
                z = 0
                for d in order:
                    t = edge(z, d)
                    assert src(ctx, t) == vertices(z >> 2, z & 3)
                    z1 = z | (1 << d)
                    assert tgt(ctx, t) == vertices(z1 >> 2, z1 & 3)
                    z = z1
            w = cube(ctx, edge, sq, lambda s, t: top(3, 0, s, t))
            return w, sq

        def vertex(mode, z):
            return state_term(starts[mode], z)

        def pure(mode, z, d):
            return activate(vertex(mode, z), d)

        def bridge(z):
            return boundary_bridge(ctx, evaluate, names, vertex(0, z), vertex(1, z))

        if chain:
            def top(mask, done, s, t):
                return chart_lift(ctx, frame(modes[0], mask, done), 1, s, t)
            w, _ = use_chart(vertex, pure, bridge, top, spatial)
            finish(w, 'chain')
            continue

        def raw_vertex(mode, z):
            return state_term(fold(ctx, 1, inside(modes[mode])), z)

        def raw_edge(mode, z, d):
            return activate(raw_vertex(mode, z), d)

        def raw_top(mask, done, s, t):
            args = [high[d] if mask & (1 << d) else
                    (tgt if done & (1 << d) else src)(ctx, high[d]) for d in (0, 1)]
            if evaluate(args[0])[0][1] != evaluate(args[1])[0][0]:
                args.reverse()
            return chart_lift(ctx, args, 0, s, t)

        def raw_xy(mode, s, t):
            return chart_lift(ctx, inside(frame(modes[mode], 3, 0)), 1, s, t)

        def raw_link(z):
            return raw_top(0, z, raw_vertex(0, z), raw_vertex(1, z))

        w, raw_face = use_chart(raw_vertex, raw_edge, raw_link, raw_top, raw_xy)
        pair = evaluate(raw_vertex(0, 0))
        assert evaluate(w)[0:2] == pair[0:2]
        assert evaluate(w)[-2:] == (EMPTY_ROW,) * 2
        counts['horizontal'] += 1
        if certify and 'horizontal' not in certified:
            certify('horizontal', w, infer(ctx, w))
            certified.add('horizontal')

        def spread(pair, a, b):
            # Two 3-arrows sharing a 2-face in one slot, with m fixed in the other.
            tree = ((), ())
            roots = (tree, ()) if pure_first else ((), tree)
            generic = tree_ctx((roots,))
            args = (*pair, fixed) if pure_first else (fixed, *pair)
            return lift_on(ctx, generic, args, a, b)

        def whisk_xy(mode, s, t):
            orders = ((0, 1), (1, 0))
            a, b = [(raw_edge(mode, 0, d), raw_edge(mode, 1 << d, e)) for d, e in orders]
            xy = raw_face(mode << 2, 0, 1)
            return fold(ctx, 3, (spread(a, s, whisk(src(ctx, xy))), whisk(xy),
                                 spread(b, whisk(tgt(ctx, xy)), t)))

        stages = []
        for side in (0, 1):
            def stage_vertex(mode, z):
                return vertex(side, z) if mode == side else whisk(raw_vertex(side, z))
            def stage_single(mode, z, d):
                return pure(side, z, d) if mode == side else whisk(raw_edge(side, z, d))
            def stage_link(z):
                return chart_lift(ctx, frame(modes[side], 0, z), 1, stage_vertex(0, z), stage_vertex(1, z))
            def stage_xy(mode, s, t):
                return spatial(side, s, t) if mode == side else whisk_xy(side, s, t)
            def stage_top(mask, done, s, t):
                return chart_lift(ctx, frame(modes[side], mask, done), 1, s, t)
            w, _ = use_chart(stage_vertex, stage_single, stage_link, stage_top, stage_xy)
            finish(w, 'regroup')
            stages.append([stage_link(z) for z in range(4)])
        for z in range(4):
            assembled = fold(ctx, 2, (stages[0][z], whisk(raw_link(z)), stages[1][z]))
            assert assembled == bridge(z)

    assert counts == {'chain': 2, 'regroup': 4, 'horizontal': 2}
    print('Corner prisms by constituent arity:', dict(counts))


def check_native(data):
    """Identify the prescribed faces and the possible block orders of each native lift."""
    ctx, names, chosen = data
    evaluate = strict_interpreter(ctx, tuple(names))
    patches = [p for p in cells((3, 3)) if len(p) == 5 and
               {rank(g) for g in p[4][0]} == {(1, 3), (3, 1)}]
    assert len(patches) == 2
    tested = set()
    block_counts = Counter()
    for patch in patches:
        two = factors(patch, (2, 2))
        for m in two:
            generator, = m[4][0]
            point = rank(generator)
            hole = (2, 1) if point == (1, 3) else (1, 2)
            pair = factors(m, hole)
            assert atom(generator) in pair
            for sign in (0, 1):
                cap = face(m, sign)
                events = ordered_factors(cap, 2, {rank(g): i for i, g in enumerate(cap[3][0])})
                assert len(events) == 2 and fold(ctx, 2, [chosen[w] for w in events]) == chosen[cap]
                raw_steps = []
                for w in events:
                    parts = factors(w, hole)
                    raw = fold(ctx, 1, [chosen[c] for c in parts])
                    raw_steps.append(raw)
                    before, after = (chosen[face(w, s)] for s in (0, 1))
                    g, = w[3][0]
                    if min(rank(g)):
                        k = boundary_bridge(ctx, evaluate, names, before, src(ctx, raw))
                        l = boundary_bridge(ctx, evaluate, names, tgt(ctx, raw), after)
                        assert fold(ctx, 2, [t for t in (k, raw, l) if t is not None]) == chosen[w]
                    else:
                        x = names[face(atom(g), 0)[2][0][0]]
                        assert raise_argument(ctx, before, x, names[g]) == chosen[w]
                        assert raise_argument(ctx, src(ctx, raw), x, names[g]) == raw

                # Distribute the stationary spatial factor through the two tile moves.
                left, right = (face(c, sign) if len(c) == 5 else c for c in pair)
                tile_first = len(left) == 4
                tile, fixed = (left, right) if tile_first else (right, left)
                tile_steps = ordered_factors(tile, 2, {rank(g): i for i, g in enumerate(tile[3][0])})
                args = [chosen[w] for w in tile_steps]
                assert fold(ctx, 2, args) == chosen[tile]
                tree = (((), ()), ()) if tile_first else ((), ((), ()))
                slots = (*args, chosen[fixed]) if tile_first else (chosen[fixed], *args)
                a = fold(ctx, 2, raw_steps)
                b = comp2(ctx, 1, chosen[left], chosen[right])
                witness = lift_on(ctx, tree_ctx((tree,)), slots, a, b)
                assert infer(ctx, witness) == arrow(ctx, a, b)
                assert evaluate(witness) == cap + (EMPTY_ROW,)
                tested.add((m, sign))

        for ordering in ((0, 1), (1, 0)):
            owner = {rank(g): i for i, g in zip(ordering, patch[4][0])}
            for w in ordered_factors(patch, 3, owner):
                g, = w[4][0]
                site = rank(g)[0]
                block = {site-1, site}
                exterior = 3 if site == 1 else 0
                neighbor = 2 if site == 1 else 1
                def group(p):
                    r = p[0]
                    return 'P' if sum(p) == 4 or r in block else ('X' if r == exterior else 'e')
                upper = {p: group(p) for p in profile(w) if sum(p) > 2}
                legal = set()
                for order in permutations(('P', 'e', 'X')):
                    pieces = ordered_factors(w, 2, {p: order.index(v) for p, v in upper.items()})
                    word = tuple(group(rank(t[-1][0][0])) for t in pieces)
                    if word != order:
                        continue
                    legal.add(word)
                    p, x, e = (pieces[word.index(k)] for k in ('P', 'X', 'e'))
                    assert p[4][0] == (g,) and len(p[3][0]) == 2
                    hole = (2, 1) if site == 1 else (1, 2)
                    assert atom(g) in factors(p, hole)
                    assert rank(x[3][0][0]) == (exterior, 3-exterior)
                    assert rank(e[3][0][0])[0] == neighbor
                assert 1 <= len(legal) <= 2
                if len(legal) == 2:
                    a, b = legal
                    assert a.index('e') == b.index('e') and a.index('e') != 1
                block_counts[len(legal)] += 1
    assert len(tested) == 8
    print(f'{len(tested)} native mixed faces and full-step orders {dict(sorted(block_counts.items()))}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    data = extend(extend(two_by_two(), (2, 2), 0, 3, None), (3, 2), 1, 3, None)
    check_native(data)
    check(data, emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Pure changes of the actual corner bridges.'))
