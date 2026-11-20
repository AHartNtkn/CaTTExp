"""Check a depth-two action with two adjacent marks and a lower spatial whisker."""
import argparse
from functools import cache
from pathlib import Path

from catt import (comp2, disc_tree, glue_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, subst_ty, tdim, tdim_tm, tgt, tree_ctx, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_exterior_actions import certificate, coherence
from gray_globe_sector_terms import arrow
from gray_globe_strip_squares import chart_lift, lift_on
from gray_leaf_naturality import marked_leaves


def check(d, emitter):
    m, n = d + 1, d + 2
    old = ctx = tree_ctx(disc_tree(1) + disc_tree(n))
    f, z = map(v, maximal_vars(old))
    ys = [src(old, z), tgt(old, z)]
    xs = [src(old, ys[0]), tgt(old, ys[0])]
    plus = list(map(v, range(len(old))))

    def declare(ty):
        nonlocal ctx
        term = v(len(ctx))
        ctx += (ty,)
        return term

    def join(k, a, b):
        return comp2(ctx, k, a, b)

    def chain(k, *terms):
        result = terms[0]
        for term in terms[1:]:
            result = join(k, result, term)
        return result

    def frame(term):
        return join(0, f, term)

    changes = {}
    for x in (*xs, *ys, z):
        xp = plus[x[1]] = declare(subst_ty(infer(old, x), plus))
        a, b = x, xp
        if x not in xs:
            a, b = join(d, a, changes[xs[1]]), join(d, changes[xs[0]], b)
        if x == z:
            a, b = join(m, a, changes[ys[1]]), join(m, changes[ys[0]], b)
        changes[x] = declare(arrow(ctx, a, b))
    rs, rt = (changes[x] for x in xs)
    hs, ht = (changes[y] for y in ys)
    zp = plus[z[1]]
    raw, final = join(d, frame(z), frame(rt)), join(d, frame(rs), frame(zp))
    inner_old, inner_new = join(d, z, rt), join(d, rs, zp)
    left, right = frame(inner_old), frame(inner_new)

    def spatial(k, a, b, s, t):
        wedge = glue_tree(tdim_tm(ctx, a), k, tdim_tm(ctx, b))
        return lift_on(ctx, tree_ctx(disc_tree(1) + wedge), (f, a, b), s, t)

    def distribute(x, y, reverse=False):
        l, u = join(d, frame(x), frame(y)), frame(join(d, x, y))
        return spatial(d, x, y, u, l) if reverse else spatial(d, x, y, l, u)

    pre = [distribute(y, rt) for y in ys]
    post = [distribute(rs, plus[y[1]], True) for y in ys]
    pre_square = spatial(d, z, rt, join(m, raw, pre[1]), join(m, pre[0], left))
    post_square = spatial(d, rs, zp, join(m, right, post[1]), join(m, post[0], final))
    middle = frame(changes[z])
    k = [frame(hs), frame(ht)]
    start = spatial(m, inner_old, ht, join(m, left, k[1]), src(ctx, middle))
    end = spatial(m, hs, inner_new, tgt(ctx, middle), join(m, k[0], right))
    main_square = chain(n, start, middle, end)

    def assoc(a, b, c, reverse=False):
        l, u = join(m, join(m, a, b), c), join(m, a, join(m, b, c))
        return chart_lift(ctx, (a, b, c), m, u, l) if reverse else chart_lift(ctx, (a, b, c), m, l, u)

    def paste(a, b, c, h, g, first, second):
        steps = (assoc(a, h[1], g[1], True), join(m, first, g[1]), assoc(h[0], b, g[1]),
                 join(m, h[0], second), assoc(h[0], g[0], c, True))
        return chain(n, *steps), [join(m, u, w) for u, w in zip(h, g, strict=True)]

    partial, side = paste(raw, left, right, pre, k, pre_square, main_square)
    action, faces = paste(raw, right, final, side, post, partial, post_square)

    # Change the elementary writing with the slot still formal. Instantiate
    # its lifted comparison at the turn between two composite m-cells.
    slot_arity = tree_ctx(disc_tree(1) + disc_tree(m))
    l, x = map(v, maximal_vars(slot_arity))
    F = comp2(slot_arity, 0, l, x)
    G = comp2(slot_arity, d, F, ident(slot_arity, tgt(slot_arity, F)))
    J = coherence(slot_arity, F, G)
    raised, lift = marked_leaves(slot_arity, frozenset({x[1]}))
    corrections, new_faces, squares = [], [], []
    for i, y in enumerate(ys):
        h = changes[y]
        labels = sub_from(raised, ctx, dict(zip(maximal_vars(raised), (f, h), strict=True)))
        upper = subst_tm(lift(J), labels)
        g_step = subst_tm(lift(G), labels)
        a, b = src(ctx, h), tgt(ctx, h)

        def at(w):
            return sub_from(slot_arity, ctx, {l[1]: f, x[1]: w})

        ja, jb = subst_tm(J, at(a)), subst_tm(J, at(b))
        assert infer(ctx, upper) == arrow(ctx, join(m, ja, g_step), join(m, k[i], jb))
        reverse = subst_tm(coherence(slot_arity, G, F), at(b))
        replacement = chain(m, ja, g_step, reverse)
        # Compare on the arity with a single promoted slot. The substitution
        # is checked against the actual two-composite type of h.
        s, t = (k[i], replacement) if i == 0 else (replacement, k[i])
        eq = chart_lift(ctx, (f, h), 0, s, t)
        corrections.append(chain(m, pre[i], eq, post[i]))
        new_faces.append(chain(m, pre[i], replacement, post[i]))
        squares.append(upper)
    assert all(infer(ctx, h) == arrow(ctx, *ends) for h, ends in
               zip(corrections, ((faces[0], new_faces[0]), (new_faces[1], faces[1])), strict=True))
    result = chain(n, join(m, raw, corrections[1]), action, join(m, corrections[0], final))
    wanted = arrow(ctx, join(m, raw, new_faces[1]), join(m, new_faces[0], final))
    assert infer(ctx, result) == wanted

    @cache
    def top_labels(term):
        if term[0] == 'v':
            return (term,)
        return tuple(label for ty, arg in zip(term[1], term[3], strict=True)
                     if tdim(ty) + 1 == n + 1 for label in top_labels(arg))

    assert top_labels(result) == (changes[z],)
    if emitter:
        certify = certificate(emitter, ctx)
        for i, term in enumerate(squares):
            certify(f'compare-slot-{i}', term, infer(ctx, term))
        certify('double-mark-action', result, wanted)
    print(f'Checked both formal-slot comparisons and the degree-{n} action at cut {d}.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cut', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.cut < 1:
        parser.error('cut must be positive for the independent zero-cut whisker')
    out = Emitter() if args.agda else None
    check(args.cut, out)
    if out:
        args.agda.write_text(out.module(args.agda.stem, 'A depth-two cylinder with adjacent marked cells.'))
