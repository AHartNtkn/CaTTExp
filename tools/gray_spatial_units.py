"""Check the two depth-one substitutions in the complete top-string collapse."""
from argparse import ArgumentParser
from pathlib import Path
from textwrap import indent

from catt import (arr, check_ctx, comp2, disc_tree, glue_tree, infer, is_ps, maximal_vars, ps_dim,
                  restrict, src, sub_from, subst_tm, subst_ty, tdim_tm, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_constant_cylinder import coherent, correction, whisk
from gray_globe_exterior_actions import certificate, chart_preimage, coherence
from gray_penultimate_partial_actions import data, distribute, rebracket
from gray_temporal_partial_actions import action, pad, rails
from gray_top_slot_promotion import support, top_action
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import composite


def scope_checks(emitter, start, module):
    body = indent('\n'.join(emitter.checks[start:]), '  ')
    emitter.checks[start:] = [f'module {module} where\n{body}']


def compare(ctx, a, b):
    """Use the pure globular subarity of these parallel routes."""
    used = support(ctx, a) | support(ctx, b)
    chart, inc = restrict(ctx, used)
    assert is_ps(chart)
    recover = chart_preimage(chart, inc)
    result = subst_tm(coherence(chart, recover(a), recover(b)), inc)
    assert infer(ctx, result) == arr(infer(ctx, a), a, b)
    return result


def cylinder(old, selected, lowest, opposed):
    """Ordinary depth one, optionally opposing its top cells; allow either missing side."""
    ctx = ()
    ends = [[], []]
    changes = {}
    for i, ty in enumerate(old):
        for e in (0, 1):
            if not e or i in selected:
                term = v(len(ctx))
                ctx += (subst_ty(ty, ends[e]),)
            assert infer(ctx, term) == subst_ty(ty, ends[e])
            ends[e].append(term)
        if i not in selected:
            continue
        degree = tdim_tm(old, v(i))
        assert degree in (lowest, lowest+1)
        a, b = ends[0][i], ends[1][i]
        if degree == lowest+1:
            s, t = (top_action(old, ctx, z, ends, changes) for z in ty[2:])
            if t is not None:
                a = comp2(ctx, lowest, a, t)
            if s is not None:
                b = comp2(ctx, lowest, s, b)
            if opposed:
                a, b = b, a
        changes[i] = v(len(ctx))
        ctx += (arr(infer(ctx, a), a, b),)
    check_ctx(ctx)
    return ctx, ends, changes


def label(chart, ends, changes, caps, steps, target):
    sub = [None]*len(chart)
    for e in (0, 1):
        for i, value in enumerate(caps[e]):
            j = ends[e][i][1]
            assert sub[j] is None or sub[j] == value
            sub[j] = value
    for i, term in changes.items():
        sub[term[1]] = steps[i]
    for j, arg in enumerate(sub):
        assert infer(target, arg) == subst_ty(chart[j], sub[:j])
    return tuple(sub)


def shifted(ctx, cut, factor, cell, side):
    if cell is None:
        return factor
    return comp2(ctx, cut, factor, cell) if side else comp2(ctx, cut, cell, factor)


def binary_square(old, space, copies, changes, r):
    x, y = maximal_vars(old)
    alpha, beta = changes[x], changes[y]
    # Pasting the opposed square of x then that of y.
    first = comp2(space, r, alpha, copies[1][y])
    second = comp2(space, r, copies[0][x], beta)
    left, middle, right = src(old, v(x))[1], tgt(old, v(x))[1], tgt(old, v(y))[1]
    head = ucomp(old)
    start = shifted(space, r, subst_tm(head, copies[1]), changes.get(left), 0)
    end = shifted(space, r, subst_tm(head, copies[0]), changes.get(right), 1)
    def assoc(args, a, b):
        return rebracket(space, r, [t for t in args if t is not None], a, b)
    steps = [assoc([changes.get(left), copies[1][x], copies[1][y]], start, src(space, first)),
             first, assoc([copies[0][x], changes.get(middle), copies[1][y]],
                          tgt(space, first), src(space, second)),
             second, assoc([copies[0][x], copies[0][y], changes.get(right)], tgt(space, second), end)]
    return composite(space, r+1, [step for step in steps if step is not None])


def double(r, compound=False, one_sided=False, emitter=None):
    old = tree_ctx(glue_tree(r, r-1, r) if compound else glue_tree(r+1, r, r+1))
    ids = tuple(map(v, range(len(old))))
    marked = {i for i in range(len(old)) if tdim_tm(old, v(i)) >= r}
    if one_sided:
        marked.difference_update(tgt(old, v(i))[1] for i in maximal_vars(old))
    space, caps, change = cylinder(old, marked, r, True)
    new_marks = {t[1] for t in change.values()}
    doubled, ends, mixed = cylinder(space, new_marks, r+1, False)
    deviations, units, comparisons = {}, {}, {}
    for i in sorted(marked):
        x = v(i)
        if tdim_tm(old, x) == r:
            units[i] = ident(old, x)
            deviations[i] = comp2(old, r, units[i], units[i])
        else:
            s, t = src(old, x)[1], tgt(old, x)[1]
            for row in (deviations, units):
                a = shifted(old, r, x, row.get(s), 0)
                b = shifted(old, r, x, row.get(t), 1)
                row[i] = compare(old, a, b)
    a, b = (label(space, caps, change, (ids, ids), row, old) for row in (deviations, units))
    for i in sorted(marked):
        j = change[i][1]
        if tdim_tm(old, v(i)) == r:
            comparisons[j] = compare(old, deviations[i], units[i])
        else:
            x = v(i)
            s, t = src(old, x)[1], tgt(old, x)[1]
            es = comparisons[change[s][1]] if s in marked else None
            et = comparisons[change[t][1]] if t in marked else None
            l = comp2(old, r+1, deviations[i], comp2(old, r, x, et)) if et else deviations[i]
            u = comp2(old, r+1, comp2(old, r, es, x), units[i]) if es else units[i]
            comparisons[j] = compare(old, l, u)
    sub = label(doubled, ends, mixed, (a, b), comparisons, old)
    base = ucomp(old)
    h = ident(old, base) if compound else base
    poles = (src(old, h), tgt(old, h))
    d = [top_action(old, space, z, caps, change) for z in poles]
    if compound:
        alpha = coherence(space, shifted(space, r, subst_tm(h, caps[1]), d[0], 0),
                          shifted(space, r, subst_tm(h, caps[0]), d[1], 1))
    else:
        alpha = binary_square(old, space, caps, change, r)
    # Actual depth-zero actions of the two endpoints in the second cylinder.
    above = [top_action(space, doubled, z, ends, mixed) for z in (src(space, alpha), tgt(space, alpha))]
    source = shifted(doubled, r+1, subst_tm(alpha, ends[0]), above[1], 1)
    target = shifted(doubled, r+1, subst_tm(alpha, ends[1]), above[0], 0)
    given = arr(infer(doubled, source), source, target)
    # Independently form the two rows by varying only the two moving poles.
    side = [top_action(space, old, z, (a, b), comparisons) if z else None for z in d]
    first = comp2(old, r, h, side[1]) if side[1] else None
    last = comp2(old, r, side[0], h) if side[0] else None
    aa, bb = subst_tm(alpha, a), subst_tm(alpha, b)
    l = shifted(old, r+1, aa, first, 1)
    u = shifted(old, r+1, bb, last, 0)
    wanted = arr(infer(old, l), l, u)
    assert subst_ty(given, sub) == wanted
    out = compare(old, l, u)
    if compound:
        # Both spatial promotions are now genuine globular arities.
        assert is_ps(doubled)
        witness = coherence(doubled, source, target)
        assert infer(doubled, witness) == given
        out = subst_tm(witness, sub)
    assert infer(old, out) == wanted and not top_counts(old, out)
    if emitter:
        p, g, sig = emitter.ctx(doubled), emitter.ctx(old), emitter.sub(sub)
        emitter.checks.append(
            f'second-sub : {g} ⊢sub {sig} ∶ {p}\n'
            f'second-sub = from-just (checkSub {g} (from-just (checkCtx {g})) {sig} {p})\n'
            f'second : ∀ {{j}} → {p} ⊢tm j ∶ {emitter.ty(given)} → '
            f'{g} ⊢tm j [ {sig} ]tm ∶ {emitter.ty(wanted)}\n'
            f'second j = S.tm[] (λ ()) j second-sub\n')
        start = len(emitter.checks)
        certificate(emitter, old)('specialized-square', out, wanted)
        scope_checks(emitter, start, 'Square')


def right_unit(ctx, a):
    n = tdim_tm(ctx, a)
    def pair(chart, x):
        return comp2(chart, n-1, x, ident(chart, tgt(chart, x))), x
    return coherent(ctx, disc_tree(n), (a,), pair, False)


def cancel_correction(ctx, forward, reverse):
    """Cancel the disk correction against the specific reverse chosen by the disk formula."""
    n = tdim_tm(ctx, forward)
    k = n-1
    assert forward[1] == reverse[1]
    chart = forward[1]
    word = comp2(ctx, k, forward, reverse)
    goal = ident(ctx, src(ctx, forward))
    if ps_dim(chart) < n:
        assert forward[3] == reverse[3]
        ids = tuple(map(v, range(len(chart))))
        a, b = (('coh', chart, t[2], ids) for t in (forward, reverse))
        step = compare(chart, comp2(chart, k, a, b), ident(chart, src(chart, a)))
        result = subst_tm(step, forward[3])
    else:
        slots = maximal_vars(chart)
        a, b = [forward[3][i] for i in slots]
        c, d = [reverse[3][i] for i in slots]
        if tdim_tm(ctx, a) == tdim_tm(ctx, b) == n:
            inner = cancel_correction(ctx, b, c)
            start = comp2(ctx, k, comp2(ctx, k, a, comp2(ctx, k, b, c)), d)
            assoc = rebracket(ctx, k, (a, b, c, d), word, start)
            middle = comp2(ctx, k, comp2(ctx, k, a, inner), d)
            unit = comp2(ctx, k, right_unit(ctx, a), d)
            result = composite(ctx, n, [assoc, middle, unit, cancel_correction(ctx, a, d)])
        else:
            side = int(tdim_tm(ctx, b) == n)
            x, y, rail = (b, d, a) if side else (a, c, b)
            j = tdim_tm(ctx, rail)-1
            collect = distribute(ctx, k, x, y, [(j, rail)], side, True)
            middle = whisk(ctx, j, cancel_correction(ctx, x, y), rail, side)
            base = src(ctx, x)
            shape = glue_tree(j+1, j, k) if side else glue_tree(k, j, j+1)
            labels = (rail, base) if side else (base, rail)
            def unit_pair(ar, l, r):
                z, h = (r, l) if side else (l, r)
                return whisk(ar, j, ident(ar, z), h, side), ident(ar, whisk(ar, j, z, h, side))
            finish = coherent(ctx, shape, labels, unit_pair, False)
            result = composite(ctx, n, [collect, middle, finish])
    assert (src(ctx, result), tgt(ctx, result)) == (word, goal)
    return result


def substituted_disk(old, target, copies, changes, w, hw, disk_action):
    """Factor two collapsed top inputs through a disk labelled by a nonvariable pole."""
    r = tdim_tm(old, w)
    disk = tree_ctx(disc_tree(r))
    top, = maximal_vars(disk)
    tau = sub_from(disk, old, {top: w})
    selected = {i for i, z in enumerate(tau) if support(old, z) & changes.keys()}
    dc, ends, moves = data(disk, frozenset(selected))
    temporal = {i: hw if i == top else changes[tau[i][1]] for i in selected}
    caps = [tuple(subst_tm(z, cp) for z in tau) for cp in copies]
    tau_up = label(dc, ends, moves, caps, temporal, target)
    q = tree_ctx(glue_tree(r+1, r, r+1))
    edges = maximal_vars(q)
    deg = ident(disk, v(top))
    red = sub_from(q, disk, {i: deg for i in edges})
    marked = {i for i, z in enumerate(red) if support(disk, z) & selected}
    qc, qends, qm = data(q, frozenset(marked))
    unit = [correction(dc, cp[top], [*rails(disk, v(top), moves, e), moves[top]], e, bool(e))
            for e, cp in enumerate(ends)]
    hdeg = comp2(dc, r+1, *unit)
    lifts = {i: hdeg if i in edges else moves[red[i][1]] for i in marked}
    red_up = label(qc, qends, qm, [tuple(subst_tm(z, cp) for z in red) for cp in ends], lifts, dc)
    full = tuple(subst_tm(z, tau_up) for z in red_up)
    for i, z in enumerate(full):
        assert infer(target, z) == subst_ty(qc[i], full[:i])
    for i in edges:
        assert subst_tm(red[i], tau) == ident(old, w)
        assert full[qm[i][1]] == disk_action


def collapse(r, emitter, certify_paste=False):
    tree = glue_tree(r, r-1, r)
    old = tree_ctx(tree)
    w = ucomp(old)
    marks = frozenset({0, *range(2, len(old))})
    ctx, copies, h = data(old, marks)
    hw, check, _ = action(tree, marks)
    assert check == ctx and top_counts(ctx, hw)
    slots = maximal_vars(old)
    moved = {copy[i][1] for copy in copies for i in slots}
    moved.update(h[i][1] for i in slots)
    space, ends, changes = cylinder(ctx, moved, r, True)
    ids = tuple(map(v, range(len(ctx))))
    def disk(x, hx):
        squares = [correction(ctx, subst_tm(x, copy), [*rails(old, x, h, e), hx], e, bool(e))
                   for e, copy in enumerate(copies)]
        return comp2(ctx, r+1, *squares)
    steps = {copy[i][1]: ident(ctx, copy[i]) for copy in copies for i in slots}
    steps.update({h[i][1]: disk(v(i), h[i]) for i in slots})
    sub = label(space, ends, changes, (ids, ids), steps, ctx)
    pure_ids = tuple(map(v, range(len(old))))
    dw = top_action(old, old, w, (pure_ids, pure_ids), {i: ident(old, v(i)) for i in slots})
    p = compare(old, dw, ident(old, w))
    pure = [pad(ctx, old, w, h, e)(subst_tm(p, cp)) for e, cp in enumerate(copies)]
    hp = disk(w, hw)
    substituted_disk(old, ctx, copies, h, w, hw, hp)
    ds, dt = (top_action(ctx, space, z, ends, changes) for z in (src(ctx, hw), tgt(ctx, hw)))
    a = comp2(space, r, ds, subst_tm(hw, ends[1]))
    b = comp2(space, r, subst_tm(hw, ends[0]), dt)
    ty = subst_ty(arr(infer(space, a), a, b), sub)
    # Quantify over the collapsed spatial square; check both sides of its required unit law.
    j = v(len(ctx))
    ext = ctx + (ty,)
    left = comp2(ext, r+1, comp2(ext, r, pure[0], hw), hp)
    right = comp2(ext, r+1, j, comp2(ext, r, hw, pure[1]))
    assert infer(ext, left) == infer(ext, right)
    if certify_paste:
        # Supply the normalized depth-one equation and construct the action at the raw disk faces.
        f = comp2(ext, r, pure[0], hw)
        rr = [*rails(old, w, h, 1), hw]
        raw = subst_tm(w, copies[1])
        rho, back = [correction(ctx, raw, rr, 1, rev) for rev in (False, True)]
        lam = correction(ctx, subst_tm(w, copies[0]), [*rails(old, w, h, 0), hw], 0, False)
        k = r+1
        normal_a = comp2(ext, k, f, lam)
        normal_b = comp2(ext, k, right, rho)
        witness = v(len(ext))
        ext += (arr(infer(ext, normal_a), normal_a, normal_b),)
        middle = comp2(ext, k, witness, back)
        enter = rebracket(ext, k, (f, lam, back), left, src(ext, middle))
        loop = cancel_correction(ctx, rho, back)
        use = comp2(ext, k, right, loop)
        assoc = rebracket(ext, k, (right, rho, back), tgt(ext, middle), src(ext, use))
        result = composite(ext, k+1, [enter, middle, assoc, use, right_unit(ext, right)])
        wanted = arr(infer(ext, left), left, right)
        assert infer(ext, result) == wanted
        assert top_counts(ext, result) == {witness[1]: 1}
    if emitter:
        g, s, sig = emitter.ctx(ctx), emitter.ctx(space), emitter.sub(sub)
        emitter.checks.append(
            f'collapse-sub : {g} ⊢sub {sig} ∶ {s}\n'
            f'collapse-sub = from-just (checkSub {g} (from-just (checkCtx {g})) {sig} {s})\n')
        start = len(emitter.checks)
        certify = certificate(emitter, ext)
        certify('unit-left', left, infer(ext, left))
        certify('unit-right', right, infer(ext, left))
        if certify_paste:
            certify('disk-action-from-unit', result, wanted)
        scope_checks(emitter, start, 'Disk')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('rank', type=int)
    parser.add_argument('--agda', type=Path)
    parser.add_argument('--paste', action='store_true', help='certify the final disk paste')
    args = parser.parse_args()
    if args.rank < 2:
        parser.error('rank must be at least two')
    out = Emitter() if args.agda else None
    if out:
        out.checks.append('import CaTTExp.Subst ∅ cattSide as S')
    for degree in range(2, args.rank+1):
        use = out if degree == args.rank else None
        double(degree, emitter=use)
        double(degree, one_sided=True)
        double(degree, compound=True)
        collapse(degree, use, args.paste)
        print(f'Rank {degree}: two-sided and one-sided squares, a composite pole, and a total collapse.', flush=True)
    if out:
        args.agda.write_text(out.module(args.agda.stem, 'The spatial unit in a total string collapse.'))
