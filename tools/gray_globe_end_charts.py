"""Verify the two end charts and the signed face specializations for a full diagonal."""
import argparse
from collections import Counter
from functools import cache
from pathlib import Path

from catt import comp2, infer, maximal_vars, src, sub_from, subst_tm, tgt, tree_ctx, v
from emit_agda import Emitter
from gray_globe_comparison import atom
from gray_globe_corner_pullback import labelled_tableaux
from gray_globe_corner_prisms import fold
from gray_globe_exterior_actions import arity, certificate
from gray_globe_factorizations import rank, truncate
from gray_globe_middle_steps import chart_tree
from gray_globe_pure_extension import raise_argument
from gray_globe_run_transport import box, extend, peak, positions, restrict, split
from gray_globe_section import cells, row_map
from gray_globe_sector_terms import arrow
from gray_globe_strip_squares import chart_lift, lift_on


def span(cell, degree):
    row = cell[degree][0]
    return rank(row[0])[0], rank(row[-1])[0]


def peel(c, k, end):
    first, last = span(c, k)
    assert first < last
    h = (first+1, last) if end == first else (first, last-1)
    groups = sorted((h, (end, end)))
    parts = split(c, k-1, groups)
    at = next(i for i, p in enumerate(parts) if span(p, k) == h)
    return parts, at


def flatten(z, k, first_end, second_end):
    parts, at = peel(z, k, first_end)
    inner, _ = peel(parts[at], k, second_end)
    return parts[:at] + inner + parts[at+1:]


def check_outer_exchange(z, k):
    lo, hi = span(z, k)
    assert lo == 0 or hi == k
    a, b = flatten(z, k, hi, lo), flatten(z, k, lo, hi)
    if a == b:
        return 'same order'
    mid, = (p for p in a if span(p, k) == (lo+1, hi-1))
    assert mid in b and (a.index(mid) == b.index(mid) in (0, 2))
    first = a.index(mid) == 2
    pair, other = (a[:2], b[:2]) if first else (a[1:], b[1:])
    pure = lo if lo == 0 else hi
    if span(pair[0], k) != (pure, pure):
        pair, other = other, pair
    pure_before, after = pair
    before, pure_after = other
    assert span(pure_before, k) == span(pure_after, k) == (pure, pure)
    assert pure_before[-1] == pure_after[-1]
    globe = atom(pure_before[-1][0][0])
    x, = globe[-2][0]
    y, = globe[-2][1]
    assert row_map(before, 0, lambda g: y if g == x else g) == after
    assert all(x in chain for chain in before[k-1])
    assert x not in {g for row in atom(before[-1][0][0]) for chain in row for g in chain}
    return 'pure swap'


def check(m, n):
    @cache
    def domain(u, v):
        return set(labelled_tableaux(u, v))
    ambient = domain(m, n)
    if max(m, n) <= 5:
        assert ambient == cells((m, n)) - {()}
    branches, pure_checks = Counter(), Counter()
    polarized = set()
    for c in ambient:
        k = len(c)-1
        if k and len(c[k][0]) == len(positions(m, n, k)):
            first, last = span(c, k)
            if last-first >= 2 and (first == 0 or last == k):
                pure_checks[check_outer_exchange(c, k)] += 1
        for d, row in enumerate(c):
            if len(row[0]) != len(positions(m, n, d)):
                break
        else:
            continue
        k = d-1
        a, b = span(c, d)
        if b-a+1 != len(c[d][0]):
            continue
        start, stop = span(c, k)
        lo, hi = max(0, a-1), min(k, b)
        if (lo, hi) == (start, stop):
            continue
        s, t = (truncate(c, k, i) for i in (0, 1))
        if a == 0 or b == k+1:
            if a == b:
                site = (0, k) if a == 0 else (k, 0)
                x, = (g for g in s[k][0] if rank(g) == site)
                y, = (g for g in t[k][0] if rank(g) == rank(x))
                assert row_map(s, 0, lambda g: y if g == x else g) == t
            else:
                axis = int(a == 0)
                bounds = [m, n]
                bounds[axis] = k
                def clip(g):
                    return tuple((r, 2 if j == axis and r == k else tag)
                                 for j, (r, tag) in enumerate(g))
                clipped = tuple(row_map(z, 0, clip) for z in (s, t))
                assert set(clipped) <= domain(*bounds)
                aa, bb = (a+1, b) if a == 0 else (a, b-1)
                assert (max(0, aa-1), min(k, bb)) == (lo, hi)
                raw = extend(peak(*box(*bounds, k, aa, bb)), *bounds, k, *clipped)
                assert raw in domain(*bounds)
                polarized.add((k, s, t))
        for end in (start, stop):
            if lo <= end <= hi:
                continue
            parts, at = peel(c, k, end)
            active, fixed = parts[at], parts[1-at]
            h = span(active, k)
            u, v = box(m, n, k-1, *h)
            smaller = restrict(active, m, n, k-1, *h)
            assert smaller in domain(u, v)
            assert len(fixed) == k+1 and span(fixed, k) == (end, end)
            box2 = box(u, v, k, a, b)
            assert box2 == box(m, n, k, a, b)
            assert restrict(smaller, u, v, k, a, b) == restrict(c, m, n, k, a, b)
            for side, state in enumerate((s, t)):
                states, state_at = peel(state, k, end)
                assert state_at == at and states[1-at] == fixed
                assert states[at] == truncate(active, k, side)
                assert restrict(states[at], m, n, k-1, *h) == truncate(smaller, k, side)
            aa, bb = span(smaller, k+1)
            assert (aa, bb) == (a, b)
            if len(smaller[k+1][0]) == len(positions(u, v, k+1)):
                kind = 'whole native hom'
            elif len(restrict(smaller, u, v, k, a, b)[k][0]) < len(smaller[k][0]):
                kind = 'padded native run'
            else:
                kind = 'native signed face'
            branches[kind] += 1
    print(f'D^{m} tensor D^{n}: {sum(branches.values())} end-chart instances {dict(branches)}; '
          f'{len(polarized)} exterior pairs specialized; {dict(pure_checks)}.')


def check_slide(d, emitter):
    """Slide a pure change past a nontrivial change of brackets with an arbitrary native arrow."""
    k = d+1
    ctx = arity(d-1, (d, k, d))
    left, change, fixed = map(v, maximal_vars(ctx))
    x0, x1 = src(ctx, change), tgt(ctx, change)
    def native(x):
        return comp2(ctx, d-1, left, x)
    def frame(w):
        return comp2(ctx, d-1, w, fixed)
    def chosen(x):
        return comp2(ctx, d-1, left, comp2(ctx, d-1, x, fixed))
    q = v(len(ctx))
    ctx += (infer(ctx, native(x0)),)
    forward = v(len(ctx))
    ctx += (arrow(ctx, native(x1), q),)
    backward = v(len(ctx))
    ctx += (arrow(ctx, q, native(x0)),)
    certify = certificate(emitter, ctx) if emitter else None

    # Build the action on a variable first, so it also applies to composite arguments.
    generic = arity(d-1, (k, d))
    move, tail = map(v, maximal_vars(generic))
    hole = src(generic, move)
    raised = raise_argument(generic, comp2(generic, d-1, hole, tail), hole, move)
    def action(w):
        sigma = sub_from(generic, ctx, {move[1]: w, tail[1]: fixed})
        return subst_tm(raised, sigma)
    def then(*terms):
        return fold(ctx, d, terms)
    native_change = raise_argument(ctx, native(x0), x0, change)
    chosen_change = raise_argument(ctx, chosen(x0), x0, change)
    framed_change = action(native_change)
    assert framed_change == raise_argument(ctx, frame(native(x0)), x0, change)

    for at_start, middle in ((True, forward), (False, backward)):
        corrections = []
        for x in (x0, x1):
            a, b = chosen(x), frame(native(x))
            ends = (a, b) if at_start else (b, a)
            corrections.append(chart_lift(ctx, (left, x, fixed), d-1, *ends))
        c0, c1 = corrections
        if at_start:
            natural = chart_lift(ctx, (left, change, fixed), d-1,
                                 then(c0, framed_change), then(chosen_change, c1))
            steps = (native_change, middle)
        else:
            natural = chart_lift(ctx, (left, change, fixed), d-1,
                                 then(framed_change, c1), then(c0, chosen_change))
            steps = (middle, native_change)
        composite = action(then(*steps))
        separate = then(*map(action, steps))
        layout = tree_ctx(chart_tree((d-1, (d, k, k), d)))
        distribute = lift_on(ctx, layout, (*steps, fixed), composite, separate)
        fm = action(middle)
        if at_start:
            before, after = then(c0, composite), then(then(chosen_change, c1), fm)
            regroup = chart_lift(ctx, (c0, framed_change, fm), d,
                                 then(c0, separate), then(then(c0, framed_change), fm))
            proof = fold(ctx, k, (then(c0, distribute), regroup, then(natural, fm)))
        else:
            before, after = then(composite, c1), then(fm, then(c0, chosen_change))
            regroup = chart_lift(ctx, (fm, framed_change, c1), d,
                                 then(separate, c1), then(fm, then(framed_change, c1)))
            proof = fold(ctx, k, (then(distribute, c1), regroup, then(fm, natural)))
        wanted = arrow(ctx, before, after)
        assert infer(ctx, proof) == wanted
        if certify:
            certify('initial-change' if at_start else 'terminal-change', proof, wanted)
    print(f'Both pure slides checked at degree {k+1} with an arbitrary native {k}-arrow.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if min(args.m, args.n) < 1:
        parser.error('require positive globe dimensions')
    check(args.m, args.n)
    emitter = Emitter() if args.agda else None
    check_slide(3, emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Sliding the pure change at either end of a native arrow.'))
