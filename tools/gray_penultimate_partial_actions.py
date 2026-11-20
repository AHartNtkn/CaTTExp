"""Transport an exact cylinder across suspension when its immediate faces are temporal strings."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from pathlib import Path

from canonical_gray_two_discs import tableau_interpreter
from catt import (STAR, arr, comp2, disc_tree, glue_tree, infer, maximal_vars, ps_boundary_vars,
                  ps_dim, restrict, src, sub_from, subst_tm, subst_ty, tdim, tdim_tm, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident, susp_ctx, susp_tm, susp_ty
from emit_agda import Emitter
from gray_constant_cylinder import coherent, whisk
from gray_globe_branch_comparisons import cylinder
from gray_globe_exterior_actions import certificate, coherence
from gray_partial_cylinder_sections import presentation, selections
from gray_path_wedge import compose
from gray_globe_section import trim
from rc2 import kappa, rc2_full
from gray_temporal_partial_actions import action, chart_comparison
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import composite, string_tree


def data(old, marks):
    ctx, minus, change = cylinder(old, marks)
    plus = [v(m[1]+1) if i in marks else m for i, m in enumerate(minus)]
    return ctx, (minus, plus), change


def face_action(old, marks, copies, change, sign):
    dim = ps_dim(old)-1
    ar, inc = restrict(old, ps_boundary_vars(old, dim, sign))
    indices = [x[1] for x in inc]
    marked = frozenset(i for i, j in enumerate(indices) if j in marks)
    if not marked:
        return None
    tree = string_tree(dim-1, [dim]*len(maximal_vars(ar)))
    assert tree_ctx(tree) == ar
    h, small, _ = action(tree, marked)
    _, ends, shifts = data(ar, marked)
    ren = [None]*len(small)
    for i, j in enumerate(indices):
        for e in (0, 1):
            ren[ends[e][i][1]] = copies[e][j]
        if i in shifts:
            ren[shifts[i][1]] = change[j]
    return subst_tm(h, ren)


def boundary_rails(old, head, change, sides, e):
    face = (tgt if not e else src)(old, head)
    poles = [sides[1-e]]
    ty = infer(old, face)
    while ty != STAR:
        _, ty, s, t = ty
        poles.append(change.get((s if e else t)[1]))
    return tuple(reversed(poles))


def pad(ctx, term, rails, side):
    for k, h in enumerate(rails):
        if h is not None:
            term = whisk(ctx, k, term, h, side)
    return term


def caps(old, ctx, copies, change, marks):
    head = ucomp(old)
    sides = [face_action(old, marks, copies, change, sign) for sign in ('-', '+')]
    result = [pad(ctx, subst_tm(head, copy), boundary_rails(old, head, change, sides, e), e)
              for e, copy in enumerate(copies)]
    return result, sides


def distribute(ctx, cut, x, y, rails, side, reverse):
    """Whiskering a temporal product versus multiplying the whiskered factors."""
    comparison = None
    for k, rail in rails:
        inner = glue_tree(cut+1-k, cut-k, cut+1-k)
        pair_tree = disc_tree(1)+inner if side else inner+disc_tree(1)
        for _ in range(k):
            pair_tree = (pair_tree,)

        def pair(ar, *terms):
            a, b, h = (terms[1], terms[2], terms[0]) if side else terms
            return (whisk(ar, k, comp2(ar, cut, a, b), h, side),
                    comp2(ar, cut, whisk(ar, k, a, h, side), whisk(ar, k, b, h, side)))

        args = (rail, x, y) if side else (x, y, rail)
        step = coherent(ctx, pair_tree, args, pair, reverse)
        if comparison is not None:
            earlier = whisk(ctx, k, comparison, rail, side)
            step = comp2(ctx, cut+1, step, earlier) if reverse else comp2(ctx, cut+1, earlier, step)
        comparison = step
        x, y = whisk(ctx, k, x, rail, side), whisk(ctx, k, y, rail, side)
    return comparison


def brackets(ar, cut, terms):
    if len(terms) == 1:
        yield terms[0]
        return
    for i in range(1, len(terms)):
        for a in brackets(ar, cut, terms[:i]):
            for b in brackets(ar, cut, terms[i:]):
                yield comp2(ar, cut, a, b)


def rebracket(ctx, cut, terms, a, b):
    if a == b:
        return None
    ar = tree_ctx(string_tree(cut, [cut+1]*len(terms)))
    slots = maximal_vars(ar)
    sub = sub_from(ar, ctx, dict(zip(slots, terms, strict=True)))
    wanted = {a: None, b: None}
    for option in brackets(ar, cut, [v(i) for i in slots]):
        val = subst_tm(option, sub)
        if val in wanted:
            wanted[val] = option
    assert all(x is not None for x in wanted.values())
    return subst_tm(coherence(ar, wanted[a], wanted[b]), sub)


def square_on_cap(tree, old, ctx, copy, change, e):
    """Compare the two routes in the pure chart, then apply the fixed higher rails."""
    head = ucomp(old)
    dim = ps_dim(old)
    cut = dim-1
    raw = subst_tm(head, copy)
    labels = [copy[i] for i in maximal_vars(old)]
    pole = src(old, src(old, head)) if e else tgt(old, tgt(old, head))
    poles = [pole]
    while infer(old, pole) != STAR:
        pole = (src if e else tgt)(old, pole)
        poles.append(pole)
    rails = [(k, change[x[1]]) for k, x in enumerate(reversed(poles)) if k and x[1] in change]

    def padded(t):
        for k, h in rails:
            t = whisk(ctx, k, t, h, e)
        return t

    shifts = [None, None]
    if 1-e in change:
        rail = change[1-e]
        whole = whisk(ctx, 0, raw, rail, e)
        inside = subst_tm(head, sub_from(old, ctx, {
            i: whisk(ctx, 0, copy[i], rail, e) for i in maximal_vars(old)}))
        for f, sign in enumerate(('-', '+')):
            face = (src, tgt)[f]
            a, b = face(ctx, whole), face(ctx, inside)
            boundary, incl = restrict(old, ps_boundary_vars(old, cut, sign))
            shape = string_tree(cut-1, [cut]*len(maximal_vars(boundary)))
            face_labels = [copy[incl[i][1]] for i in maximal_vars(boundary)]
            chart = disc_tree(1)+shape if e else shape+disc_tree(1)
            args = [rail]+face_labels if e else face_labels+[rail]
            shifts[f] = chart_comparison(ctx, chart, args, b, a) if e else chart_comparison(ctx, chart, args, a, b)
        a, b = (inside, whole) if e else (whole, inside)
        first = (a, shifts[1])
        last = (shifts[0], b)
        chart = disc_tree(1)+tree if e else tree+disc_tree(1)
        args = [rail]+labels if e else labels+[rail]
        h = chart_comparison(ctx, chart, args, comp2(ctx, cut, *first), comp2(ctx, cut, *last))
        steps = [distribute(ctx, cut, *first, rails, e, True), padded(h),
                 distribute(ctx, cut, *last, rails, e, False)]
        square = composite(ctx, dim, [t for t in steps if t is not None])
        shifts = [padded(t) for t in shifts]
    else:
        whole = inside = raw
        square = None
    return square, shifts, (padded(whole), padded(inside))


def paste_squares(ctx, dim, middle, wanted, outer_faces, correction_data):
    cut = dim-1
    squares, adjustments, cap_parts = zip(*correction_data)
    left, right = adjustments
    # Split the source and target of the transferred cylinder into cap + temporal face.
    def operands(t):
        return [t[3][i] for i in maximal_vars(t[1])]
    dminus, hv = operands(src(ctx, middle))
    hu, dplus = operands(tgt(ctx, middle))
    assert dminus == cap_parts[0][1] and dplus == cap_parts[1][1]
    cminus, cplus = cap_parts[0][0], cap_parts[1][0]
    for f, h in enumerate((hu, hv)):
        assert outer_faces[f] == composite(ctx, cut, [x for x in (left[f], h, right[f]) if x is not None])

    state = wanted[0]
    path = []

    def advance(step, labels):
        nonlocal state
        assoc = rebracket(ctx, cut, [x for x in labels if x is not None], state, src(ctx, step))
        if assoc is not None:
            path.append(assoc)
        path.append(step)
        state = tgt(ctx, step)

    if squares[0] is not None:
        h = comp2(ctx, cut, squares[0], hv)
        if right[1] is not None:
            h = comp2(ctx, cut, h, right[1])
        advance(h, (cminus, left[1], hv, right[1]))
    h = middle
    if left[0] is not None:
        h = comp2(ctx, cut, left[0], h)
    if right[1] is not None:
        h = comp2(ctx, cut, h, right[1])
    advance(h, (left[0], dminus, hv, right[1]))
    if squares[1] is not None:
        h = comp2(ctx, cut, hu, squares[1])
        if left[0] is not None:
            h = comp2(ctx, cut, left[0], h)
        advance(h, (left[0], hu, dplus, right[1]))
    labels = [x for x in (left[0], hu, right[0], cplus) if x is not None]
    assoc = rebracket(ctx, cut, labels, state, wanted[1])
    if assoc is not None:
        path.append(assoc)
    result = composite(ctx, dim, path)
    ty = arr(infer(ctx, wanted[0]), *wanted)
    assert infer(ctx, result) == ty
    return result, ty


def transport(inner_tree, inner_term, ends, check_writing=False):
    tree = (inner_tree,)
    old = tree_ctx(tree)
    dim = ps_dim(old)
    cut = dim-1
    inner = tree_ctx(inner_tree)
    full = frozenset(range(len(inner)))
    marks = frozenset({*ends, *range(2, len(old))})
    ctx, copies, change = data(old, marks)
    lo, hi = copies
    lower, lc, lh = data(inner, full)
    oldcaps, _ = caps(inner, lower, lc, lh, full)
    inner_ty = arr(infer(lower, oldcaps[0]), *oldcaps)
    # The induction hypothesis may be kept formal for a stand-alone implication.
    formal = inner_term is None
    if formal:
        inner_term = v(len(lower))
    else:
        assert infer(lower, inner_term) == inner_ty
    sigma = [lo[0], hi[1]]+[None]*len(lower)
    for i in range(len(inner)):
        for e in (0, 1):
            cap = copies[e][i+2]
            if 1-e in ends:
                cap = whisk(ctx, 0, cap, change[1-e], e)
            sigma[lc[e][i][1]+2] = cap
        sigma[lh[i][1]+2] = change[i+2]
    if formal:
        ctx += (subst_ty(susp_ty(inner_ty), sigma),)
        sigma.append(v(len(ctx)-1))
    middle = subst_tm(susp_tm(inner_term), sigma)
    wanted, outer_faces = caps(old, ctx, copies, change, marks)
    head = ucomp(old)
    correction_data = [square_on_cap(tree, old, ctx, copy, change, e) for e, copy in enumerate(copies)]
    result, ty = paste_squares(ctx, dim, middle, wanted, outer_faces, correction_data)
    expected = (Counter({len(ctx)-1: 1}) if formal else
                Counter(change[i][1] for i in maximal_vars(old) if tdim(old[i])+1 == dim))
    assert top_counts(ctx, result) == expected
    if check_writing:
        other = comp2(old, cut, ident(old, src(old, head)), head)
        adjusted = result
        for e, copy in enumerate(copies):
            a, b = (head, other) if e else (other, head)
            h = subst_tm(coherence(old, a, b), copy)
            h = pad(ctx, h, boundary_rails(old, head, change, outer_faces, e), e)
            adjusted = comp2(ctx, dim, adjusted, h) if e else comp2(ctx, dim, h, adjusted)
        other_caps = [pad(ctx, subst_tm(other, copy), boundary_rails(old, other, change, outer_faces, e), e)
                      for e, copy in enumerate(copies)]
        assert infer(ctx, adjusted) == arr(infer(ctx, other_caps[0]), *other_caps)
        assert top_counts(ctx, adjusted) == expected
    return result, ctx, ty


def check_replacement(tree, marks):
    """Replace each immediate pole of an existing operation by a different raw term."""
    old = tree_ctx(tree)
    dim = ps_dim(old)
    cut = dim-1
    w = ucomp(old)
    ctx, copies, change = data(old, marks)
    original, sides = caps(old, ctx, copies, change, marks)
    assert all(h is not None for h in sides)
    middle = v(len(ctx))
    ctx += (arr(infer(ctx, original[0]), *original),)
    poles, pure = [], []
    for f, sign in enumerate(('-', '+')):
        ar, inc = restrict(old, ps_boundary_vars(old, cut, sign))
        x = ucomp(ar)
        other = (comp2(ar, cut-1, ident(ar, src(ar, x)), x) if not f else
                 comp2(ar, cut-1, x, ident(ar, tgt(ar, x))))
        poles.append(subst_tm(other, inc))
        pure.append([subst_tm(coherence(ar, a, b), inc)
                     for a, b in ((other, x), (x, other))])
    c = coherence(old, *poles)
    correction_data = []
    for e, copy in enumerate(copies):
        lower = boundary_rails(old, w, change, sides, e)[:-1]
        rails = [(k, h) for k, h in enumerate(lower) if h is not None]
        a, b = (w, c) if e else (c, w)
        first = (a, pure[1][e])
        last = (pure[0][e], b)
        square = coherence(old, comp2(old, cut, *first), comp2(old, cut, *last))
        x, y = (subst_tm(t, copy) for t in first)
        before = distribute(ctx, cut, x, y, rails, e, True)
        x, y = (subst_tm(t, copy) for t in last)
        after = distribute(ctx, cut, x, y, rails, e, False)
        steps = [before, pad(ctx, subst_tm(square, copy), lower, e), after]
        shifts = [pad(ctx, subst_tm(row[e], copy), lower, e) for row in pure]
        caps_pair = [pad(ctx, subst_tm(t, copy), lower, e) for t in (c, w)]
        correction_data.append((composite(ctx, dim, [t for t in steps if t is not None]),
                                shifts, caps_pair))
    new_sides = [composite(ctx, cut, [correction_data[0][1][f], h, correction_data[1][1][f]])
                 for f, h in enumerate(sides)]
    wanted = [pad(ctx, subst_tm(c, copy), boundary_rails(old, c, change, new_sides, e), e)
              for e, copy in enumerate(copies)]
    result, _ = paste_squares(ctx, dim, middle, wanted, new_sides, correction_data)
    assert top_counts(ctx, result) == {middle[1]: 1}


def base_action(tree, marks):
    """Lift the induced strict 3-cell, correcting actual one- and two-faces."""
    old = tree_ctx(tree)
    ctx, copies, change = data(old, marks)
    wanted, _ = caps(old, ctx, copies, change, marks)
    _, _, _, _, atoms, groups = presentation(tree, marks)
    evaluate = tableau_interpreter(ctx, atoms.__getitem__)
    a, b = map(evaluate, wanted)
    top = tuple(sorted(change[i][1] for i in maximal_vars(old) if i in marks and tdim(old[i])+1 == 2))
    target = a[:-1] + ((a[-1][0], b[-1][0]), (top, top))
    cells = {cell for group in groups.values() for cell in group}
    assert target in cells

    def poles(t, k):
        s = u = t
        for _ in range(tdim_tm(ctx, t)-k):
            s, u = src(ctx, s), tgt(ctx, u)
        return s, u

    def adjust(t, k, s, u):
        left, right = poles(t, k)
        compare = kappa if k == 1 else rc2_full
        if left != s:
            t = comp2(ctx, k, compare(ctx, s, left), t)
        if right != u:
            t = comp2(ctx, k, t, compare(ctx, right, u))
        return t

    @cache
    def build(cell):
        intrinsic = trim(cell)
        if intrinsic in atoms:
            return v(atoms.index(intrinsic))
        for k in range(len(intrinsic)-1):
            starts = [x for x in cells if x[:k] == cell[:k] and x[k][0] == cell[k][0]
                      and k+1 < len(trim(x)) and all(set(s) <= set(t) for i in range(k+1, 4)
                      for s, t in zip(x[i], cell[i]))]
            for x in sorted(starts):
                for y in sorted(cells):
                    if k+1 >= len(trim(y)) or x[:k] != y[:k] or x[k][1] != y[k][0]:
                        continue
                    if compose(x, y, k) != cell:
                        continue
                    left, right = build(x), build(y)
                    if k:
                        shared = poles(left, k)[1]
                        if k == 2:
                            right = adjust(right, 1, src(ctx, shared), tgt(ctx, shared))
                        _, after = poles(right, k)
                        right = adjust(right, k, shared, after)
                    result = comp2(ctx, k, left, right)
                    assert trim(evaluate(result)) == intrinsic
                    return result
        raise AssertionError(intrinsic)

    term = build(target)
    while tdim_tm(ctx, term) < 3:
        term = ident(ctx, term)
    term = adjust(term, 1, src(ctx, wanted[0]), tgt(ctx, wanted[0]))
    term = adjust(term, 2, *wanted)
    assert infer(ctx, term) == arr(infer(ctx, wanted[0]), *wanted)
    assert evaluate(term) == target
    return term


def check_fixed_ends(tree):
    old = tree_ctx(tree)
    count = 0
    for marks in selections(old):
        if not marks:
            continue
        term = base_action(tree, marks)
        lower, _, _ = data(old, marks)
        outer = tree_ctx((tree,))
        shifted = frozenset(i+2 for i in marks)
        ctx, copies, change = data(outer, shifted)
        assert ctx == susp_ctx(lower)
        wanted, _ = caps(outer, ctx, copies, change, shifted)
        assert infer(ctx, susp_tm(term)) == arr(infer(ctx, wanted[0]), *wanted)
        count += 1
    print(f'{count} base actions and their suspensions at two fixed endpoints.', flush=True)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('dimension', type=int)
    parser.add_argument('--agda', type=Path)
    parser.add_argument('--base', action='store_true', help='construct the base 3-term as well')
    parser.add_argument('--selections', action='store_true', help='check every base selection with fixed outer endpoints')
    args = parser.parse_args()
    if args.dimension < 3:
        parser.error('use a dimension of at least three')
    tree = (((),), ())
    if args.selections:
        check_fixed_ends(tree)
    term_at_full = base_action(tree, frozenset(range(len(tree_ctx(tree))))) if args.base else None
    for dim in range(3, args.dimension+1):
        for ends in ((0,), (1,), (0, 1)):
            term, ctx, wanted = transport(tree, term_at_full, ends, check_writing=True)
            if args.agda and dim == args.dimension and ends == (0, 1):
                emitter = Emitter()
                certificate(emitter, ctx)('transport', term, wanted)
                args.agda.write_text(emitter.module(args.agda.stem, 'The two distributor squares and their paste.'))
        print(f'Dimension {dim}: both one-ended transports and the full transport.', flush=True)
        check_replacement((tree,), frozenset({0, *range(2, len(tree_ctx((tree,))))}))
        if args.base:
            term_at_full = term
        tree = (tree,)
