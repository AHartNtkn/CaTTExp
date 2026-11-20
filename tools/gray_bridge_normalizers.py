"""Check simultaneous changes of normalizers and cancellation of a thin right factor."""
from argparse import ArgumentParser
from pathlib import Path

from catt import (arr, check_ctx, comp2, disc_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_exterior_actions import certificate
from gray_partial_cylinder_sections import positions
from gray_spatial_units import compare, scope_checks
from gray_thin_substitution import flat, pure_fold
from gray_top_slot_promotion import expand, top_action
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import composite, string_tree


def normalizer(ctx, term):
    step = pure_fold(ctx, term, [])
    return ident(ctx, term) if step is None else step


def bridge_triangle(r, change_both):
    # Independent raw writings of the same two lower labels, one with composite support.
    base = tree_ctx(string_tree(r-1, [r]*3))
    a, b, c = map(v, maximal_vars(base))
    ab = comp2(base, r-1, a, b)
    def pad(term, right):
        if right:
            return comp2(base, r-1, term, ident(base, tgt(base, term)))
        return comp2(base, r-1, ident(base, src(base, term)), term)
    initial = [pad(pad(ab, False), True), pad(c, False)]
    final = [ab, pad(c, True) if change_both else initial[1]]
    tree = string_tree(r-1, [r]*2)
    chart = tree_ctx(tree)
    slots = maximal_vars(chart)
    op = ucomp(chart)
    def sub(terms):
        return sub_from(chart, base, dict(zip(slots, terms, strict=True)))
    start, finish = sub(initial), sub(final)
    normalized = sub([flat(base, x) for x in initial])
    assert normalized == sub([flat(base, x) for x in final])
    root = subst_tm(op, normalized)
    last = compare(base, root, flat(base, root))
    ds = [flat(base, compare(base, x, y)) for x, y in zip(initial, final)]
    ls = [normalizer(base, x) for x in initial]
    lt = [normalizer(base, x) for x in final]
    def raised(lo, hi, steps):
        return top_action(chart, base, op, (lo, hi), dict(zip(slots, steps, strict=True)))
    d, l, m = raised(start, finish, ds), raised(start, normalized, ls), raised(finish, normalized, lt)
    left, right = comp2(base, r, l, last), comp2(base, r, m, last)
    t, u = subst_tm(op, start), subst_tm(op, finish)
    assert src(base, left) == t and src(base, right) == u
    assert tgt(base, left) == tgt(base, right) == flat(base, t) == flat(base, u)

    # The spatial compositor lives first on a two-step graft, before the labels are known.
    def graft(n):
        wide, ends, rows = expand(tree, {positions(tree)[i][0]: n for i in slots})
        return tree_ctx(wide), tuple(tuple(map(v, e)) for e in ends), rows
    two, ends, rows = graft(2)
    mids = list(ends[0])
    first, second, both = {}, {}, {}
    for i in slots:
        f, g = map(v, rows[i])
        mids[i] = tgt(two, f)
        first[i], second[i], both[i] = f, g, comp2(two, r, f, g)
    da = top_action(chart, two, op, (ends[0], mids), first)
    db = top_action(chart, two, op, (mids, ends[1]), second)
    dc = top_action(chart, two, op, ends, both)
    join = compare(two, comp2(two, r, da, db), dc)
    actual = {j: z for i, f, g in zip(slots, ds, lt) for j, z in zip(rows[i], (f, g), strict=True)}
    join = subst_tm(join, sub_from(two, base, actual))
    assert src(base, join) == comp2(base, r, d, m)

    # Vary the two change labels in the once-raised template along the two pure triangles.
    one, caps, single = graft(1)
    leaves = {i: v(single[i][0]) for i in slots}
    template = top_action(chart, one, op, caps, leaves)
    products = [comp2(base, r, f, g) for f, g in zip(ds, lt, strict=True)]
    def label(values):
        return sub_from(one, base, {single[i][0]: z for i, z in zip(slots, values, strict=True)})
    triangles = [compare(base, h, z) for h, z in zip(products, ls, strict=True)]
    vary = top_action(one, base, template, (label(products), label(ls)),
                      {single[i][0]: z for i, z in zip(slots, triangles, strict=True)})
    assert tgt(base, join) == src(base, vary) and tgt(base, vary) == l
    together = comp2(base, r+1, join, vary)
    source = comp2(base, r, d, right)
    assoc = compare(base, source, comp2(base, r, comp2(base, r, d, m), last))
    out = comp2(base, r+1, assoc, comp2(base, r, together, last))
    ty = arr(infer(base, source), source, left)
    assert infer(base, out) == ty
    # Both ends agree with the independently recursive normalizers after their unit adjustments.
    for raw, expanded in ((t, left), (u, right)):
        calculated = normalizer(base, raw)
        assert infer(base, calculated) == infer(base, expanded)
        compare(base, expanded, calculated)
    return base, out, ty


def cancellation(r):
    # Two different formal squares, with a comparison known only after appending E.
    disk = tree_ctx(disc_tree(r+2))
    alpha, = map(v, maximal_vars(disk))
    beta = v(len(disk))
    ctx = disk + (infer(disk, alpha),)
    p, q = src(ctx, alpha), tgt(ctx, alpha)
    x = tgt(ctx, p)
    y = comp2(ctx, r-1, x, ident(ctx, tgt(ctx, x)))
    assert x != y
    e, back = compare(ctx, x, y), compare(ctx, y, x)
    def extend(z):
        return comp2(ctx, r, z, e)
    def restore(z):
        return comp2(ctx, r, extend(z), back)
    enter, leave = compare(ctx, p, restore(p)), compare(ctx, restore(q), q)
    def frame(z):
        return composite(ctx, r+1, (enter, z, leave))
    a, b = (extend(z) for z in (alpha, beta))
    gamma = v(len(ctx))
    ctx += (arr(infer(ctx, a), a, b),)
    check_ctx(ctx)
    h = frame(comp2(ctx, r, gamma, back))
    assert src(ctx, h) == frame(restore(alpha)) and tgt(ctx, h) == frame(restore(beta))
    out = composite(ctx, r+2, (compare(ctx, alpha, src(ctx, h)), h, compare(ctx, tgt(ctx, h), beta)))
    ty = arr(infer(ctx, alpha), alpha, beta)
    assert infer(ctx, out) == ty and top_counts(ctx, out) == {gamma[1]: 1}
    return ctx, out, ty


def association(r, lengths):
    # Flatten the outer and inner normal heads in either order.
    def path(n):
        return tree_ctx(string_tree(r-1, [r]*n))
    def subdivision(shape, target, sizes):
        edges = list(map(v, maximal_vars(target)))
        offset = 0
        labels = {}
        for x, size in zip(maximal_vars(shape), sizes, strict=True):
            if size:
                term = composite(target, r-1, edges[offset:offset+size])
            else:
                vertex = tgt(target, edges[offset-1]) if offset else src(target, edges[0])
                term = ident(target, vertex)
            labels[x] = flat(target, term)
            offset += size
        assert offset == len(edges)
        return sub_from(shape, target, labels)
    def elementary(ctx, e):
        n = flat(ctx, e)
        return ident(ctx, e) if n == e else compare(ctx, e, n)
    outer, middle, final = path(2), path(4), path(sum(lengths))
    rho = subdivision(outer, middle, (2, 2))
    tau = subdivision(middle, final, lengths)
    c = ucomp(outer)
    e = subst_tm(c, rho)
    ne = flat(middle, e)
    top_first = comp2(final, r, subst_tm(elementary(middle, e), tau),
                      elementary(final, subst_tm(ne, tau)))
    raw = tuple(subst_tm(w, tau) for w in rho)
    slots = maximal_vars(outer)
    exact = sub_from(outer, final, {i: flat(final, raw[i]) for i in slots})
    changes = {i: elementary(final, raw[i]) for i in slots}
    inner = top_action(outer, final, c, (raw, exact), changes)
    inner_first = comp2(final, r, inner, elementary(final, subst_tm(c, exact)))
    t = subst_tm(e, tau)
    ty = arr(infer(final, t), t, flat(final, t))
    assert infer(final, top_first) == infer(final, inner_first) == ty
    assert top_first != inner_first
    return final, compare(final, top_first, inner_first)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    out = Emitter() if args.agda else None
    for r in (1, 2, 3):
        for both in (False, True):
            triple = bridge_triangle(r, both)
            if out and r == 1 and both:
                ctx, term, ty = triple
                start = len(out.checks)
                certificate(out, ctx)('common-normalizer', term, ty)
                scope_checks(out, start, 'Triangle')
        ctx, term, ty = cancellation(r)
        if out and r == 1:
            start = len(out.checks)
            certificate(out, ctx)('cancel-bridge', term, ty)
            scope_checks(out, start, 'Cancellation')
        for lengths in ((2, 1, 1, 2), (2, 0, 1, 2)):
            ctx, term = association(r, lengths)
            if out and r == 1 and lengths[1] == 0:
                start = len(out.checks)
                certificate(out, ctx)('associativity-boundary', term, infer(ctx, term))
                scope_checks(out, start, 'Associativity')
        print(f'Checked normalizer triangles, right cancellation and both flattening orders at rank {r}.',
              flush=True)
    if args.agda:
        args.agda.write_text(out.module(args.agda.stem, 'Normalizer triangles and cancellation of a right bridge.'))
