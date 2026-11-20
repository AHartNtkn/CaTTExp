"""Check the exact faces of iterated threshold padding on a mixed whiskering arity."""
import argparse
from functools import cache
from pathlib import Path

from canonical_gray_two_discs import tableau_interpreter
from catt import comp2, infer, maximal_vars, src, tdim_tm, tgt, v
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_adjacent_thresholds import step_at
from gray_globe_comparison import atom, face
from gray_globe_cubical_corner import map_rows
from gray_globe_exterior_actions import arity, certificate
from gray_globe_factorizations import truncate
from gray_globe_sector_terms import arrow
from gray_globe_strip_squares import chart_lift
from gray_globe_threshold_faces import image


def check(p, t, j, emitter):
    d, k = p + t - 1, p + j
    ctx = arity(d, (k, d + 1))
    g, cap = map(v, maximal_vars(ctx))
    native = atom(((p, 2), (j, 2)))
    values = {}

    def assign(slot, rows):
        if slot in values:
            assert values[slot] == rows
            return
        values[slot] = rows
        if len(rows) > 1:
            for side, end in enumerate((src, tgt)):
                assign(end(ctx, slot), face(rows, side))

    assign(g, map_rows(native, lambda h: image(h, p, t - 1, 0)))
    assign(cap, step_at(truncate(native, d, 1), p, t))
    assert len(values) == len(ctx)
    evaluate = tableau_interpreter(ctx, lambda index: values[v(index)])

    @cache
    def pole(w, degree, side):
        if tdim_tm(ctx, w) == degree:
            return w
        return pole((src, tgt)[side](ctx, w), degree, side)

    def head(w, initial, final):
        return chart_lift(ctx, (w, cap), d, initial, final)

    @cache
    def chosen(w):
        degree = tdim_tm(ctx, w)
        if degree == d + 1:
            raw = comp2(ctx, d, w, cap)
        else:
            raw = head(w, chosen(src(ctx, w)), chosen(tgt(ctx, w)))
        # Distinct writings for the new faces force genuine lower corrections.
        return comp2(ctx, degree - 1, raw, ident(ctx, tgt(ctx, raw)))

    def prefix(w, last):
        result = chosen(w)
        for i in range(d + 1, last + 1):
            result = comp2(ctx, i, change(pole(w, i, 0)), result)
        return result

    def suffix(w, last):
        result = comp2(ctx, d, w, cap)
        for i in range(d + 1, last + 1):
            result = comp2(ctx, i, result, change(pole(w, i, 1)))
        return result

    @cache
    def change(w):
        last = tdim_tm(ctx, w) - 1
        return head(w, suffix(w, last), prefix(w, last))

    s, u = src(ctx, g), tgt(ctx, g)
    last = k - 2
    left, right = change(s), change(u)
    reverse_left = head(s, tgt(ctx, left), src(ctx, left))
    forward = comp2(ctx, k - 1, suffix(g, last), right)
    incoming = comp2(ctx, k - 1, reverse_left, forward)
    assert infer(ctx, incoming) == arrow(ctx, prefix(s, last), prefix(u, last))
    target = map_rows(native, lambda h: image(h, p, t, 0))
    assert evaluate(incoming) == target

    certify = certificate(emitter, ctx) if emitter else None
    for i in range(last, d, -1):
        preimage = prefix(g, i - 1)
        reapplied = comp2(ctx, i, change(pole(g, i, 0)), preimage)
        assert infer(ctx, preimage) == arrow(ctx, prefix(s, i - 1), prefix(u, i - 1))
        assert infer(ctx, reapplied) == infer(ctx, incoming) != infer(ctx, preimage)
        comparison = head(g, incoming, reapplied)
        assert evaluate(comparison) == target + (((), ()),)
        if certify:
            certify(f'peel-{i}', comparison, arrow(ctx, incoming, reapplied))
        incoming = preimage

    assert infer(ctx, incoming) == arrow(ctx, chosen(s), chosen(u))
    assert evaluate(incoming) == target
    final = comp2(ctx, k - 1, left, prefix(g, last))
    result = head(g, forward, final)
    assert evaluate(result) == target + (((), ()),)
    if certify:
        certify('generator-change', result, arrow(ctx, forward, final))
    print(f'Checked {last - d} prefix lifts and the generator change at degree {k}, cut {d}.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('p', type=int)
    parser.add_argument('t', type=int)
    parser.add_argument('j', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if min(args.p, args.t) < 1 or args.j < args.t + 2:
        parser.error('p and t must be positive and j must be at least t + 2')
    output = Emitter() if args.agda else None
    check(args.p, args.t, args.j, output)
    if output:
        args.agda.write_text(output.module(args.agda.stem, 'Iterated threshold padding on a mixed arity.'))
