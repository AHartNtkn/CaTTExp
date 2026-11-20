"""Compare adjacent threshold substitutions at the native attaching terms."""
import argparse
from collections import Counter
from itertools import product
from pathlib import Path

from canonical_gray_two_discs import tableau_interpreter
from catt import comp2, infer, maximal_vars, src, subst_tm, subst_ty, tgt, v
from emit_agda import Emitter
from gray_globe_comparison import atom, face, globe
from gray_globe_exterior_actions import certificate
from gray_globe_distant_columns import reflect
from gray_globe_factorizations import profile, truncate
from gray_globe_pure_extension import raise_argument
from gray_globe_section import EMPTY_ROW, cells
from gray_globe_sector_terms import arrow, tile
from gray_globe_shift_faces import linear, raise_column
from gray_globe_strip_squares import chart_lift
from gray_globe_cubical_corner import map_rows
from gray_globe_threshold_faces import collapse, image
from gray_path_wedge import compose


def step_at(z, p, t):
    caps = [map_rows(z, lambda g: image(g, p, t - 1, s)) for s in (0, 1)]
    assert caps[0][:-1] == caps[1][:-1]
    label, = (g for g in z[-1][0] if g[0][0] == p)
    change = ((p + 1, 2), label[1])
    return caps[0][:-1] + ((caps[0][-1][0], caps[1][-1][0]), ((change,), (change,)))


def check_strict(bound):
    counts = Counter()
    for p, n in product(range(1, bound + 1), repeat=2):
        for j, tag in globe(n):
            native = atom(((p, 2), (j, tag)))
            for t in range(1, j + 1):
                d = p + t - 1
                for e in (0, 1):
                    def previous(g):
                        return image(g, p, t - 1, e)

                    def current(g):
                        return image(g, p, t, e)

                    active = 1 - e
                    z = truncate(native, d, active)
                    changed = ((p, 2), (t - 1, active ^ (p % 2)))
                    assert changed in z[-1][0]
                    assert changed not in truncate(native, d, e)[-1][0]
                    cap = step_at(z, p, t)
                    # Check the native atom and every intermediate pole, including
                    # the pair to which syntactic naturality is applied.
                    for k in range(d + 1, p + j + 1):
                        for side in range(1 if k == p + j else 2):
                            c = truncate(native, k, side)
                            old = map_rows(c, previous)
                            pad = cap + (EMPTY_ROW,) * (len(old) - len(cap))
                            raw = compose(pad, old, d) if e else compose(old, pad, d)
                            assert raw == map_rows(c, current)
                            counts['cut products'] += 1
                            if k == d + 1:
                                labels = {g for row in c for chain in row for g in chain}
                                for g in labels:
                                    if current(g) != previous(g):
                                        assert g == changed or g[0][0] == p and g[1][0] == t
                    if j == t + 1:
                        counts['adjacent images'] += 1
    print(dict(counts))


def check_growth(bound):
    count = 0
    for n in range(1, bound + 1):
        for t, e in product(range(n + 1), (0, 1)):
            def move(g):
                return Counter(image(g, 1, t, e))

            for g in product(globe(1), globe(n)):
                raised = raise_column(g, 1, n)
                assert linear(raised, move) == linear(move(g), lambda h: raise_column(h, 1, n))
                for sign in (0, 1):
                    def include(h):
                        a, (j, y) = h
                        return a, (j, sign if j == n else y)
                    assert Counter(include(h) for h in move(g)) == move(include(g))
                count += 1
    print(f'{count} signed strip-growth instances.')


def check_opposite_crossings(m, n):
    p = m - 1
    counts = Counter()

    def factors(w, c, u, side):
        d = p + u
        z = truncate(c, d, 1 - side)
        cap = step_at(z, p, u + 1)
        if len(c) == d + 1:
            assert cap == w
            return (cap,)
        fixed = map_rows(c, lambda g: image(g, p, u, side))
        pad = cap + (EMPTY_ROW,) * (len(fixed) - len(cap))
        before, after = (pad, fixed) if side else (fixed, pad)
        assert compose(before, after, d) == w
        return before, after

    for w in cells((m, n)) - {()}:
        sites = profile(w)
        u = max((j for i, j in sites if i == m), default=-1)
        if u < 0 or (p, u + 1) in sites:
            continue
        c = collapse(w, p)
        label, = (g for g in c[p + u][0] if g[0][0] == p)
        tag = label[1][1]
        if tag == 2:
            assert w == atom(((m, 2), (u, tag)))
        other = reflect(w)
        reflected = factors(other, collapse(other, p), u, int(tag == 0))
        assert reflected == tuple(map(reflect, reversed(factors(w, c, u, int(tag == 1)))))
        counts['crossings'] += 1
    print(f'{counts["crossings"]} opposite crossing factorizations in {m} by {n}.')


def args_of(term):
    return [term[3][i] for i in maximal_vars(term[1])]


def check_terms(t, emitter):
    # In this certificate the previous substitutions are input parameters.
    # Their interpretation checks every resulting tableau in the larger box.
    p, d, n = 1, t, t + 1
    old, labels, chosen = tile(n, 1)
    index = {g: i for i, g in enumerate(labels)}
    ctx, values = (), []

    def declare(ty, value):
        nonlocal ctx
        term = v(len(ctx))
        ctx += (ty,)
        values.append(value)
        return term

    previous = [[], []]
    changes = {}
    for g, ty in zip(labels, old, strict=True):
        for e in (0, 1):
            value = map_rows(atom(g), lambda h: image(h, p, t - 1, e))
            wanted = subst_ty(ty, previous[e])
            if e and (g[0][0] < p or g[1][0] < t - 1):
                term = previous[0][-1]
                assert infer(ctx, term) == wanted and values[term[1]] == value
            else:
                term = declare(wanted, value)
            previous[e].append(term)
        if g[0][0] == p and g[1][0] == t - 1:
            changes[g] = declare(arrow(ctx, previous[0][-1], previous[1][-1]),
                                 atom(((p + 1, 2), g[1])))

    def action(term, g):
        x = v(index[g])
        formal = old + (infer(old, x),)
        y = v(len(old))
        formal += (arrow(formal, x, y),)
        up = raise_argument(formal, term, x, v(len(old) + 1))
        return subst_tm(up, (*previous[0], previous[1][index[g]], changes[g]))

    evaluate = tableau_interpreter(ctx, values.__getitem__)
    certify = certificate(emitter, ctx) if emitter else None
    for e in (0, 1):
        changed = ((p, 2), (t - 1, 1 ^ e ^ (p % 2)))
        new = []
        for g, ty in zip(labels, old, strict=True):
            term = previous[e][index[g]]
            if g == changed:
                term = previous[1 - e][index[g]]
            elif g[0][0] == p and g[1][0] == t:
                pole = chosen[face(atom(g), 1 - e)]
                cap = action(pole, changed)
                term = comp2(ctx, d, cap, term) if e else comp2(ctx, d, term, cap)
            elif g[0][0] == p and g[1][0] == n:
                native = atom(g)
                cap = action(chosen[truncate(native, d, 1 - e)], changed)
                raw = comp2(ctx, d, cap, term) if e else comp2(ctx, d, term, cap)
                corrections = []
                for side, end in enumerate((src, tgt)):
                    pole = chosen[face(native, side)]
                    left, right = args_of(pole)
                    # The native pole consists of an independent whiskered step
                    # and one old column generator, in the order set by side.
                    stationary, column = (left, right) if side == 0 else (right, left)
                    u = subst_tm(column, previous[e])
                    w0 = subst_tm(stationary, previous[e])
                    w1 = subst_tm(stationary, new)
                    initial, final = end(ctx, raw), subst_tm(pole, new)
                    if side == e:
                        letters = (w0, u, cap) if e == 0 else (cap, u, w0)
                        a, b = (initial, final) if side else (final, initial)
                        path = [chart_lift(ctx, letters, d, a, b)]
                    else:
                        # Move the change through the independent whisker using
                        # the spatial chart, then collect the three temporal slots.
                        other, = (arg for arg in args_of(stationary) if arg != v(index[changed]))
                        fixed = subst_tm(other, previous[e])
                        r = changes[changed]
                        cap_on_column = action(chosen[face(atom(labels[column[1]]), 1 - e)], changed)
                        spatial = (r, fixed) if side else (fixed, r)
                        if e == 0:
                            before = comp2(ctx, d, w0, cap)
                            after = comp2(ctx, d, cap_on_column, w1)
                            first, last = (u, w0, cap), (u, cap_on_column, w1)
                        else:
                            before = comp2(ctx, d, cap, w0)
                            after = comp2(ctx, d, w1, cap_on_column)
                            first, last = (cap, w0, u), (w1, cap_on_column, u)
                        start, end_of_swap = (before, after) if side else (after, before)
                        swap = chart_lift(ctx, spatial, d - 1, start, end_of_swap)
                        middle = comp2(ctx, d, swap, u) if e else comp2(ctx, d, u, swap)
                        if not side:
                            initial, final, first, last = final, initial, last, first
                        path = [chart_lift(ctx, first, d, initial, src(ctx, middle)), middle,
                                chart_lift(ctx, last, d, tgt(ctx, middle), final)]
                    change = path[0]
                    for h in path[1:]:
                        change = comp2(ctx, d + 1, change, h)
                    corrections.append(change)
                term = comp2(ctx, d + 1, comp2(ctx, d + 1, corrections[0], raw), corrections[1])
                if certify:
                    certify(f'adjacent-{e}', term, subst_ty(ty, new))
            assert infer(ctx, term) == subst_ty(ty, new)
            assert evaluate(term) == map_rows(atom(g), lambda h: image(h, p, t, e))
            new.append(term)
    print(f'Checked both relative substitutions through transverse rank {n} at threshold {t}.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bound', type=int)
    parser.add_argument('--terms', type=int, default=2)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if min(args.bound, args.terms) < 1:
        parser.error('bounds must be positive')
    check_strict(args.bound)
    check_growth(args.bound)
    size = min(5, args.bound)
    if size >= 2:
        check_opposite_crossings(size, size)
    out = Emitter() if args.agda else None
    check_terms(args.terms, out)
    if out:
        args.agda.write_text(out.module(args.agda.stem, 'One-sided transport between adjacent thresholds.'))
