"""Construct exact naturality terms for temporal strings in ordinary partial cylinders."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache, reduce
from pathlib import Path

from catt import (STAR, arr, chain_tree, comp2, disc_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, tdim_tm, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident, susp_tm
from gray_constant_cylinder import correction as contract_identity
from emit_agda import Emitter
from gray_globe_branch_comparisons import cylinder
from gray_globe_exterior_actions import certificate, chart_preimage, coherence
from gray_partial_cylinder_sections import selections
from relative_coherence_cut import top_counts


def chart_comparison(ctx, tree, labels, left, right):
    arity = tree_ctx(tree)
    sigma = sub_from(arity, ctx, dict(zip(maximal_vars(arity), labels, strict=True)))
    recover = chart_preimage(arity, sigma)
    a, b = recover(left), recover(right)
    assert a is not None and b is not None
    result = subst_tm(coherence(arity, a, b), sigma)
    assert (src(ctx, result), tgt(ctx, result)) == (left, right)
    return result


def rails(old, cap, changes, side):
    poles = []
    ty = infer(old, cap)
    while ty != STAR:
        _, ty, s, t = ty
        poles.append((s if side else t)[1])

    return [changes.get(i) for i in reversed(poles)]


def pad(ctx, old, cap, changes, side, start=0):
    def apply(term):
        for cut, h in enumerate(rails(old, cap, changes, side)):
            if cut >= start and h is not None:
                term = comp2(ctx, cut, h, term) if side else comp2(ctx, cut, term, h)
        return term
    return apply


def path_action(ctx, old, copies, change, edges, caps):
    minus, plus = copies
    # Move the changing seam from the last vertex to the first.
    current = caps[0]
    steps = []
    for j in reversed(range(len(edges))):
        edge = edges[j]
        if edge not in change:
            continue
        step = change[edge]
        for i in reversed(edges[:j]):
            step = comp2(ctx, 0, minus[i], step)
        for i in edges[j+1:]:
            step = comp2(ctx, 0, step, plus[i])
        seam = tgt(old, v(edge))[1]
        route = [minus[i] for i in edges[:j+1]]
        if seam in change:
            route.append(change[seam])
        route.extend(plus[i] for i in edges[j+1:])
        if current != src(ctx, step):
            steps.append(chart_comparison(ctx, chain_tree(len(route)), route, current, src(ctx, step)))
        steps.append(step)
        current = tgt(ctx, step)
    if current != caps[1]:
        seam = src(old, v(edges[0]))[1]
        route = ([change[seam]] if seam in change else []) + [plus[i] for i in edges]
        steps.append(chart_comparison(ctx, chain_tree(len(route)), route, current, caps[1]))
    return reduce(lambda a, b: comp2(ctx, 1, a, b), steps)


@cache
def action(tree, marks):
    old = tree_ctx(tree)
    ctx, minus, change = cylinder(old, marks)
    plus = [v(t[1]+1) if i in marks else t for i, t in enumerate(minus)]
    copies = (minus, plus)
    slots = maximal_vars(old)
    head = ucomp(old)
    caps = [pad(ctx, old, head, change, side)(subst_tm(head, copy))
            for side, copy in enumerate(copies)]
    if len(slots) == 1:
        result = change[slots[0]]
    elif not tree[0]:
        result = path_action(ctx, old, copies, change, slots, caps)
    else:
        inner = tree[0]
        inner_marks = frozenset(i-2 for i in marks if i >= 2)
        inner_result, _, _ = action(inner, inner_marks)
        lower, neg, h = cylinder(tree_ctx(inner), inner_marks)
        sigma = [minus[0], plus[1]] + [None]*len(lower)
        for i, m in enumerate(neg):
            a, b = minus[i+2], plus[i+2]
            sigma[m[1]+2] = comp2(ctx, 0, a, change[1]) if 1 in change else a
            if i in h:
                sigma[m[1]+3] = comp2(ctx, 0, change[0], b) if 0 in change else b
                sigma[h[i][1]+2] = change[i+2]
        result = subst_tm(susp_tm(inner_result), sigma)
        for side, endpoint in enumerate((1, 0)):
            if endpoint not in change:
                continue
            copy = copies[side]
            raw = subst_tm(head, copy)
            edge = change[endpoint]
            whole = comp2(ctx, 0, edge, raw) if side else comp2(ctx, 0, raw, edge)
            labels = [copy[i] for i in slots]
            distributed = [comp2(ctx, 0, edge, x) if side else comp2(ctx, 0, x, edge)
                           for x in labels]
            inside = subst_tm(head, sub_from(old, ctx, dict(zip(slots, distributed))))
            chart = disc_tree(1) + tree if side else tree + disc_tree(1)
            args = [edge] + labels if side else labels + [edge]
            a, b = (inside, whole) if side else (whole, inside)
            correction = chart_comparison(ctx, chart, args, a, b)
            correction = pad(ctx, old, head, change, side, 1)(correction)
            cut = tdim_tm(old, head)  # dimension of a cylinder cap
            result = comp2(ctx, cut, result, correction) if side else comp2(ctx, cut, correction, result)
    wanted = arr(infer(ctx, caps[0]), *caps)
    assert infer(ctx, result) == wanted
    assert top_counts(ctx, result) == Counter(change[i][1] for i in slots if i in marks)
    return result, ctx, wanted


def change_writing(old, ctx, copies, changes, original, action_term, other):
    assert infer(old, original) == infer(old, other)
    n = tdim_tm(old, other)
    for side, copy in enumerate(copies):
        a, b = (original, other) if side else (other, original)
        comparison = subst_tm(coherence(old, a, b), copy)
        adjustment = pad(ctx, old, original, changes, side)(comparison)
        action_term = (comp2(ctx, n, action_term, adjustment) if side else
                       comp2(ctx, n, adjustment, action_term))
    verify_faces(old, ctx, other, copies, changes, action_term)
    return action_term


def verify_faces(old, ctx, head, copies, changes, result):
    a, b = [pad(ctx, old, head, changes, side)(subst_tm(head, copy))
            for side, copy in enumerate(copies)]
    assert infer(ctx, result) == arr(infer(ctx, a), a, b)


def check_writings(tree, marks, identity=False):
    old = tree_ctx(tree)
    ctx, minus, changes = cylinder(old, marks)
    plus = [v(m[1]+1) if i in marks else m for i, m in enumerate(minus)]
    copies = (minus, plus)
    head = ucomp(old)
    if identity:
        base = head
        head = ident(old, base)
        steps = [contract_identity(ctx, subst_tm(base, copy), rails(old, head, changes, side),
                                   side, bool(side)) for side, copy in enumerate(copies)]
        term = comp2(ctx, tdim_tm(old, head), *steps)
        verify_faces(old, ctx, head, copies, changes, term)
    else:
        term, _, _ = action(tree, marks)
    # Add a literal top unitor to the cap operation, retaining its variable endpoints.
    n = tdim_tm(old, head)
    other = comp2(old, n-1, ident(old, src(old, head)), head)
    alternative = change_writing(old, ctx, copies, changes, head, term, other)
    expected = Counter() if identity else Counter(changes[i][1] for i in maximal_vars(old) if i in marks)
    assert top_counts(ctx, alternative) == expected


def check(height, width, agda):
    tree = chain_tree(width)
    for dimension in range(1, height+1):
        old = tree_ctx(tree)
        count = 0
        for marks in selections(old):
            if marks:
                check_writings(tree, marks)
                count += 1
        print(f'{width} composable {dimension}-cells: {count} exact partial actions', flush=True)
        disc = disc_tree(dimension-1)
        identity_count = 0
        for marks in selections(tree_ctx(disc)):
            if marks:
                check_writings(disc, marks, identity=True)
                identity_count += 1
        print(f'D^{dimension-1}: {identity_count} exact identity actions', flush=True)
        if dimension == height and agda:
            marks = frozenset({0, *range(2, len(old))}) if dimension > 1 else frozenset(range(len(old)))
            term, ctx, wanted = action(tree, marks)
            emitter = Emitter()
            certificate(emitter, ctx)('temporal-action', term, wanted)
            agda.write_text(emitter.module(agda.stem, 'An exact partial temporal action.'))
        tree = (tree,)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('height', type=int)
    parser.add_argument('width', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.height < 1 or args.width < 1:
        parser.error('use a positive height and a nonempty string')
    check(args.height, args.width, args.agda)
