"""Construct depth-two naturality at separated marks, including an internal seam."""
import argparse
from collections import Counter
from functools import cache
from pathlib import Path

from catt import (comp2, disc_tree, infer, maximal_vars, src, sub_from, subst_tm,
                  subst_ty, tdim, tgt, tree_ctx, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_exterior_actions import certificate
from gray_globe_sector_terms import arrow
from gray_globe_strip_squares import chart_lift, lift_on


def check_terminal(d, emitter):
    m, n = d + 1, d + 2
    # An incoming m-cell f followed by two parallel-to-parallel n-steps
    # at cut m. In the enlarged tree a second m-cell r follows this block.
    tree = ((), ((), ()))
    enlarged = (*tree, ())
    for _ in range(d):
        tree, enlarged = (tree,), (enlarged,)
    old, ctx = tree_ctx(tree), tree_ctx(enlarged)
    f, z0, z1, r = map(v, maximal_vars(ctx))
    minus = sub_from(old, ctx, dict(zip(maximal_vars(old), (f, z0, z1), strict=True)))
    ys = (src(ctx, z0), tgt(ctx, z0), tgt(ctx, z1))
    x = src(ctx, r)

    def join(cut, a, b):
        return comp2(ctx, cut, a, b)

    def temporal(*steps):
        result = steps[0]
        for step in steps[1:]:
            result = join(n, result, step)
        return result

    def declare(ty):
        nonlocal ctx
        term = v(len(ctx))
        ctx += (ty,)
        return term

    def cap(a):
        return join(d, a, r)

    nu = {x: tgt(ctx, r), **{u: cap(u) for u in (*ys, z0, z1)}}
    plus = {x: tgt(ctx, r)}
    h = []
    collapse = list(map(v, range(len(ctx))))
    for y in ys:
        a = nu[y]
        b = plus[y] = declare(infer(ctx, a))
        h.append(declare(arrow(ctx, a, b)))
        collapse += [a, ident(ctx, a)]
    # This is the contraction in each lower face. Verify every label,
    # including the triangle on h after changing its target b.
    for term, ty in zip(collapse, ctx, strict=True):
        assert infer(ctx, term) == subst_ty(ty, collapse)
    for turn in h:
        collapsed = subst_tm(turn, collapse)
        start = join(m, collapsed, turn)
        chart_lift(ctx, (turn,), m, start, turn)

    old_steps, new_steps, squares = [], [], []
    for i, z in enumerate((z0, z1)):
        before = nu[z]
        after = plus[z] = declare(arrow(ctx, plus[ys[i]], plus[ys[i+1]]))
        old_steps.append(before)
        new_steps.append(after)
        squares.append(declare(arrow(ctx, join(m, before, h[i+1]), join(m, h[i], after))))

    def sigma(images):
        result = tuple(images.get(term, term) for term in minus)
        for a, ty in zip(result, old, strict=True):
            assert infer(ctx, a) == subst_ty(ty, result)
        return result

    # A genuine old generic term with composite poles f * y0 and f * y2.
    a, b, c = map(v, maximal_vars(old))
    original = comp2(old, d, a, comp2(old, m, b, c))
    old_term, transported, new_term = (subst_tm(original, s) for s in (minus, sigma(nu), sigma(plus)))
    raw = cap(old_term)

    def frame(a):
        return join(d, f, a)

    def normalize(y):
        return chart_lift(ctx, (f, y, r), d, cap(frame(y)), frame(cap(y)))

    first, last = normalize(ys[0]), normalize(ys[-1])
    old_chart = tree_ctx(enlarged)
    epsilon = lift_on(ctx, old_chart, (f, z0, z1, r),
                      join(m, raw, last), join(m, first, transported))
    a0, a1 = old_steps
    b0, b1 = new_steps

    def assoc(a, b, c, reverse=False):
        l, r = join(m, join(m, a, b), c), join(m, a, join(m, b, c))
        return chart_lift(ctx, (a, b, c), m, r, l) if reverse else chart_lift(ctx, (a, b, c), m, l, r)

    inner = temporal(assoc(a0, a1, h[2]), join(m, a0, squares[1]),
                     assoc(a0, h[1], b1, True), join(m, squares[0], b1),
                     assoc(h[0], b0, b1))
    middle = frame(inner)
    # f * (A B) and (f * A)(f * B) are compared on the two-slot
    # temporal tree embedded after the fixed incoming cell.
    spatial = ((), ((), ()))
    for _ in range(d):
        spatial = (spatial,)
    spatial = tree_ctx(spatial)
    lower_first, lower_last = frame(h[0]), frame(h[2])
    before = lift_on(ctx, spatial, (f, join(m, a0, a1), h[2]),
                     join(m, transported, lower_last), src(ctx, middle))
    after = lift_on(ctx, spatial, (f, h[0], join(m, b0, b1)),
                    tgt(ctx, middle), join(m, lower_first, new_term))
    reduced = temporal(before, middle, after)
    action = temporal(assoc(raw, last, lower_last, True), join(m, epsilon, lower_last),
                      assoc(first, transported, lower_last), join(m, first, reduced),
                      assoc(first, lower_first, new_term, True))
    hs, ht = join(m, first, lower_first), join(m, last, lower_last)
    assert infer(ctx, action) == arrow(ctx, join(m, raw, ht), join(m, hs, new_term))

    # Supply genuinely different lower writings on both ends, then transport
    # back to them. The comparison direction is opposite at the source pole.
    def reframe(step, reverse):
        other = join(m, step, ident(ctx, tgt(ctx, step)))
        change = chart_lift(ctx, (step,), m, step if reverse else other, other if reverse else step)
        return other, change

    hs_new, source_change = reframe(hs, True)
    ht_new, target_change = reframe(ht, False)
    result = temporal(join(m, raw, target_change), action, join(m, source_change, new_term))
    wanted = arrow(ctx, join(m, raw, ht_new), join(m, hs_new, new_term))
    assert infer(ctx, result) == wanted
    if emitter:
        certify = certificate(emitter, ctx)
        certify('terminal-action', result, wanted)
    @cache
    def top_chain(term):
        if term[0] == 'v':
            return Counter({term: 1})
        return sum((top_chain(arg) for ty, arg in zip(term[1], term[3], strict=True)
                    if tdim(ty) + 1 == n + 1), Counter())

    assert top_chain(result) == Counter(squares)
    print(f'Checked the terminal action at dimension {n} with both prescribed lower faces.')


def check_interior(d, emitter):
    m, n = d + 1, d + 2

    def spatial_tree(*blocks):
        tree = tuple(disc_tree(count) if isinstance(count, int) else count for count in blocks)
        for _ in range(d):
            tree = (tree,)
        return tree_ctx(tree)

    # Keep minus on the incoming block, plus on the outgoing one.
    mid = ctx = spatial_tree(1, 0, 1)
    a, r, b = map(v, maximal_vars(mid))

    def join(cut, l, u):
        return comp2(ctx, cut, l, u)

    def declare(ty):
        nonlocal ctx
        term = v(len(ctx))
        ctx += (ty,)
        return term

    def arrows(z, incoming):
        split = []
        changes = []
        normalized = join(d, z, r) if incoming else join(d, r, z)
        for end in (src, tgt):
            anchor = end(ctx, normalized)
            other = declare(infer(ctx, anchor))
            l, u = (anchor, other) if incoming else (other, anchor)
            turn = declare(arrow(ctx, l, u))
            # The active homotopy from/to the collapsed arrow has the
            # unit triangle on the very same turn as its variable label.
            unit = ident(ctx, anchor)
            if incoming:
                chart_lift(ctx, (turn,), m, join(m, unit, turn), turn)
            else:
                chart_lift(ctx, (turn,), m, turn, join(m, turn, unit))
            split.append(other)
            changes.append(turn)
        other = declare(arrow(ctx, *split))
        before, after = (normalized, other) if incoming else (other, normalized)
        square = declare(arrow(ctx, join(m, before, changes[1]), join(m, changes[0], after)))
        return before, after, changes, square

    na, pa, ha, sa = arrows(a, True)
    nb, pb, hb, sb = arrows(b, False)
    initial, final = join(d, a, nb), join(d, pa, b)
    first = [join(d, end(ctx, a), h) for end, h in zip((src, tgt), hb)]
    last = [join(d, h, end(ctx, b)) for end, h in zip((src, tgt), ha)]
    triple = (a, r, b)
    rebracket = [chart_lift(ctx, (end(ctx, a), r, end(ctx, b)), d,
                            end(ctx, join(d, a, pb)), end(ctx, join(d, na, b)))
                 for end in (src, tgt)]
    bridge = lift_on(ctx, mid, triple, join(m, join(d, a, pb), rebracket[1]),
                     join(m, rebracket[0], join(d, na, b)))

    def distribute(variable, before, after, turns, square, left):
        def frame(x, y):
            return join(d, x, y) if left else join(d, y, x)

        def compare(bottom, top, items):
            pair = ((), ())
            blocks = (1, pair) if left else (pair, 1)
            slots = (variable, *items) if left else (*items, variable)
            return lift_on(ctx, spatial_tree(*blocks), slots, bottom, top)

        moving = frame(variable, square)
        start = join(m, frame(variable, before), frame(tgt(ctx, variable), turns[1]))
        end = join(m, frame(src(ctx, variable), turns[0]), frame(variable, after))
        pre = compare(start, src(ctx, moving), (before, turns[1]))
        post = compare(tgt(ctx, moving), end, (turns[0], after))
        return join(n, join(n, pre, moving), post)

    step_left = distribute(a, nb, pb, hb, sb, True)
    step_right = distribute(b, na, pa, ha, sa, False)

    def paste(old, new, h, j, k, left_square, right_square):
        # Paste the squares for the consecutive strips old -> j -> new.
        def associate(x, y, z, reverse=False):
            l, u = join(m, join(m, x, y), z), join(m, x, join(m, y, z))
            return chart_lift(ctx, (x, y, z), m, u, l) if reverse else chart_lift(ctx, (x, y, z), m, l, u)
        path = (associate(old, h[1], k[1], True), join(m, left_square, k[1]),
                associate(h[0], j, k[1]), join(m, h[0], right_square),
                associate(h[0], k[0], new, True))
        result = path[0]
        for step in path[1:]:
            result = join(n, result, step)
        return result, [join(m, p, q) for p, q in zip(h, k, strict=True)]

    between = join(d, na, b)
    part, faces = paste(initial, between, first, join(d, a, pb), rebracket, step_left, bridge)
    result, faces = paste(initial, final, faces, between, last, part, step_right)
    wanted = arrow(ctx, join(m, initial, faces[1]), join(m, faces[0], final))
    assert infer(ctx, result) == wanted
    if emitter:
        certificate(emitter, ctx)('interior-action', result, wanted)
    print(f'Checked both moving blocks of an interior mark in dimension {n}.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cut', type=int)
    parser.add_argument('--agda', type=Path)
    parser.add_argument('--interior', action='store_true')
    args = parser.parse_args()
    if args.cut < 0:
        parser.error('cut must be nonnegative')
    out = Emitter() if args.agda else None
    if args.interior:
        check_interior(args.cut, out)
    else:
        check_terminal(args.cut, out)
    if out:
        args.agda.write_text(out.module(args.agda.stem, 'Depth-two naturality at a separated variable.'))
