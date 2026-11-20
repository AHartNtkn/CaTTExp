"""Identify the lower open frames on the middle event and paste their comparison."""
import argparse
from collections import Counter
from itertools import product
from pathlib import Path

from catt import comp2, infer, maximal_vars, src, tgt, v
from emit_agda import Emitter
from gray_globe_comparison import globe
from gray_globe_corner_prisms import fold
from gray_globe_end_charts import flatten, peel, span
from gray_globe_exterior_actions import arity, certificate
from gray_globe_factorizations import truncate
from gray_globe_middle_parameter import full_state, native_part, writing
from gray_globe_pure_extension import raise_argument
from gray_globe_run_transport import peak
from gray_globe_sector_terms import arrow
from gray_globe_strip_squares import chart_lift


def retained_frame(bounds, retained, degree, end):
    """Recover the lower operations by peeling the whole higher factor."""
    parts, active_index = peel(retained, degree, end)
    active, fixed = parts[active_index], parts[1-active_index]
    assert len(fixed) == degree + 1 and len(active) == len(retained)
    active_op, native, smaller, include = native_part(bounds, degree, active)
    fixed_op, _, _, _ = native_part(bounds, degree, fixed)
    return (active_index, fixed_op, active_op), native, smaller, include


def check_state(bounds, k, bits):
    m, n = bounds
    d = k - 1
    first, last = k - n, m
    state = full_state(m, n, k, bits)
    middle = None
    end_steps = []
    for first_end, next_end, lower_first, lower_next in (
        (first, last, first - 1, last), (last, first, last, first - 1)
    ):
        parts, at = peel(state, k, first_end)
        retained = parts[at]
        _, native, smaller, _ = native_part(bounds, k, retained)
        outer, value, outer_box, include_outer = retained_frame(bounds, retained, d, lower_first)
        assert (smaller, native) == (outer_box, value)
        inner_parts, inner_at = peel(native, k, next_end)
        inner, w, inner_box, include_inner = retained_frame(smaller, inner_parts[inner_at], d, lower_next)
        word = flatten(state, k, first_end, next_end)
        crossing, = (part for part in word if span(part, k) == (next_end, next_end))
        step_frame, step_native, step_box, _ = retained_frame(bounds, crossing, d, lower_first)
        assert step_frame == outer and step_box == smaller
        assert step_native == inner_parts[1 - inner_at]
        for side in (0, 1):
            corner = truncate(crossing, d, side)
            corner_parts, active_index = peel(corner, d, lower_first)
            assert active_index == outer[0]
            fixed_op, _, _, _ = native_part(bounds, d, corner_parts[1 - active_index])
            active_op, local_state, _, _ = native_part(bounds, d, corner_parts[active_index])
            assert (active_index, fixed_op, active_op) == outer
            assert local_state == truncate(step_native, d, side)
        end_steps.append(tuple(part for part in word if span(part, k) in
                               ((first, first), (last, last))))
        mid, = (part for part in word if span(part, k) == (first + 1, last - 1))
        assert middle is None or middle == mid
        middle = mid
        before = {span(part, k)[0] for part in word[:word.index(mid)]}
        assert (first in before) == (bits[0] == 0)
        assert (last in before) == (bits[-1] == 1)
        for side in (0, 1):
            state_at_middle = truncate(mid, d, side)
            lower_bits = (1 - bits[0],) + (side,) * (last - first - 1) + (bits[-1],)
            assert state_at_middle == full_state(m, n, d, lower_bits)
            signature, pole, lower_box, include = writing(bounds, d, state_at_middle, lower_first, lower_next)
            assert outer + inner == signature and inner_box == lower_box == (m - 1, n - 1)
            assert pole == truncate(w, d, side) == truncate(peak(*lower_box), d, side)
            for g in product(globe(m - 1), globe(n - 1)):
                assert include(g) == include_outer(include_inner(g))


    path, other_path = end_steps
    if bits[0] == bits[-1]:
        assert path == other_path
    else:
        assert path[0][-1] == other_path[1][-1] and path[1][-1] == other_path[0][-1]
        assert truncate(path[0], d, 0) == truncate(other_path[0], d, 0)
        assert truncate(path[1], d, 1) == truncate(other_path[1], d, 1)
        for route in end_steps:
            assert truncate(route[0], d, 1) == truncate(route[1], d, 0)


def check_bounds(limit):
    counts = Counter()
    for m, n in product(range(3, limit + 1), repeat=2):
        for k in range(max(m, n) + 1, m + n - 1):
            for bits in product((0, 1), repeat=m + n - k):
                check_state((m, n), k, bits)
                counts['pure lower end' if k - 1 == max(m, n) else 'mixed lower ends'] += 1
    print(f'Both middle frames at both poles through bound {limit}: {dict(counts)}.')


def check_paste(d, emitter):
    """Compose two side comparisons with the naturality square on the native input."""
    k = d + 1
    ctx = arity(d - 1, (k, k, k))
    left, middle, right = map(v, maximal_vars(ctx))
    l0, p0, r0 = (src(ctx, t) for t in (left, middle, right))
    l1, p1, r1 = (tgt(ctx, t) for t in (left, middle, right))

    def first(x, w, y):
        return comp2(ctx, d - 1, comp2(ctx, d - 1, x, w), y)

    def second(x, w, y):
        return comp2(ctx, d - 1, x, comp2(ctx, d - 1, w, y))

    def word(*terms):
        return fold(ctx, d, terms)

    def spatial(slots, a, b):
        return chart_lift(ctx, slots, d - 1, a, b)

    def rebracket(slots, a, b):
        return chart_lift(ctx, slots, d, a, b)

    start, finish = first(l0, p0, r0), second(l1, p1, r1)
    u0, v0 = (f(l1, p0, r0) for f in (first, second))
    u1, v1 = (f(l1, p1, r0) for f in (first, second))
    a_u, a_v = (spatial((left, p0, r0), start, t) for t in (u0, v0))
    b_u, b_v = (spatial((l1, p1, right), s, finish) for s in (u1, v1))
    e0 = spatial((l1, p0, r0), u0, v0)
    e1 = spatial((l1, p1, r0), u1, v1)
    p_u, p_v = (raise_argument(ctx, t, p0, middle) for t in (u0, v0))
    change = spatial((l1, middle, r0), word(p_u, e1), word(e0, p_v))
    prefix = spatial((left, p0, r0), word(a_u, e0), a_v)
    suffix = spatial((l1, p1, right), b_u, word(e1, b_v))
    result = fold(ctx, k, (
        word(a_u, p_u, suffix),
        rebracket((a_u, p_u, e1, b_v), word(a_u, p_u, word(e1, b_v)),
                  word(a_u, word(p_u, e1), b_v)),
        word(a_u, change, b_v),
        rebracket((a_u, e0, p_v, b_v), word(a_u, word(e0, p_v), b_v),
                  word(a_u, e0, p_v, b_v)),
        word(prefix, p_v, b_v),
    ))
    wanted = arrow(ctx, word(a_u, p_u, b_u), word(a_v, p_v, b_v))
    assert infer(ctx, result) == wanted
    if emitter:
        certificate(emitter, ctx)('comparison', result, wanted)
    print(f'Checked side and middle pasting in degree {k + 1}.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bound', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.bound < 3:
        parser.error('mixed end tests start at bound three')
    check_bounds(args.bound)
    out = Emitter() if args.agda else None
    check_paste(3, out)
    if out:
        args.agda.write_text(out.module(args.agda.stem, 'Paste end comparisons around the middle change.'))
