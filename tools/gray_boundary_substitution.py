"""Check the boundary substitution and the stationary entries in a spatial promotion."""
from argparse import ArgumentParser
from pathlib import Path

from catt import (arr, comp2, infer, maximal_vars, src, sub_from, subst_tm, tdim_tm, tgt,
                  tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_exterior_actions import certificate, coherence
from gray_partial_cylinder_sections import positions
from gray_spatial_units import binary_square, compare, cylinder, label, scope_checks
from gray_thin_substitution import flat
from gray_top_slot_promotion import expand, top_action
from rc2 import rc2_full
from relative_coherence_exchange_faces import composite, string_tree


def expansion(tree, lengths):
    ctx = tree_ctx(tree)
    slots = maximal_vars(ctx)
    addresses = positions(tree)
    wide, ends, stacks = expand(tree, {addresses[i][0]: n for i, n in zip(slots, lengths, strict=True) if n})
    target = tree_ctx(wide)
    changes = {}
    for i in slots:
        edges = stacks.get(i, [])
        if edges:
            r = tdim_tm(ctx, v(i))
            row = tree_ctx(string_tree(r, [r+1]*len(edges)))
            sub = sub_from(row, target, dict(zip(maximal_vars(row), map(v, edges), strict=True)))
            changes[i] = subst_tm(ucomp(row), sub)
        else:
            changes[i] = ident(target, v(ends[0][i]))
    return target, tuple(tuple(map(v, cp)) for cp in ends), changes


def boundary(r, lengths):
    # The middle formal position is labelled by a strict identity one rank down.
    tree = string_tree(r-1, [r]*3)
    base = tree_ctx(tree)
    slots = maximal_vars(base)
    p, ends, changes = expansion(tree, lengths)
    q, qe, _ = expansion(tree, (1, 1, 1))
    x, y, z = map(v, slots)
    final = [comp2(base, r-1, x, y), ident(base, tgt(base, y)), z]
    initial = [comp2(base, r-1, w, ident(base, tgt(base, w))) for w in final]
    t0, t1 = [sub_from(base, base, dict(zip(slots, row, strict=True))) for row in (initial, final)]
    du = {}
    bridges = {}
    local = {}
    for i in slots:
        b = compare(base, t0[i], t1[i])
        bridges[i] = flat(base, b)
        d = top_action(base, p, t1[i], ends, changes)
        if i == slots[1]:
            assert d is None
            d = ident(p, subst_tm(t1[i], ends[0]))
        du[i] = d
        local[i] = flat(p, comp2(p, r, subst_tm(bridges[i], ends[0]), d))
    # The two substitutions originate in the very same head arity.
    qa = maximal_vars(q)
    sig = sub_from(q, p, dict(zip(qa, local.values(), strict=True)))
    low = sub_from(q, base, dict(zip(qa, bridges.values(), strict=True)))
    w = ucomp(base)
    u = comp2(base, r-1, ident(base, src(base, w)), w)
    head = coherence(q, subst_tm(u, qe[0]), subst_tm(w, qe[1]))
    actual, collapsed = (subst_tm(head, sub) for sub in (sig, low))
    orig = subst_tm(u, t0)
    dest = subst_tm(w, t1)
    link = compare(base, u, w)
    left_bridge = subst_tm(link, t0)
    inner = top_action(base, base, w, (t0, t1), bridges)
    first = comp2(base, r, left_bridge, inner)
    assert infer(base, collapsed) == infer(base, first) == arr(infer(base, orig), orig, dest)
    literal = tuple(subst_tm(dest, cp) for cp in ends)
    tcaps = tuple(tuple(subst_tm(t, cp) for t in t1) for cp in ends)
    reduced = {i: d for i, d in du.items() if i != slots[1]}
    nested = top_action(base, p, w, tcaps, reduced)
    direct = top_action(base, p, dest, ends, changes)
    padded = top_action(base, p, w, tcaps, du)
    assert nested == direct and padded != direct
    assert (src(p, direct), tgt(p, direct)) == literal
    missing_unit = compare(p, padded, direct)
    assert infer(p, missing_unit) == arr(infer(p, padded), padded, direct)
    # Compare the divided and direct routes at the literal normal writings.
    normal_bridge = flat(base, collapsed)
    pre = subst_tm(first, ends[0])
    post = subst_tm(normal_bridge, ends[0])
    divided = comp2(p, r, pre, padded)
    reference = comp2(p, r, post, direct)
    normal = flat(p, actual)
    reduce_boundary = subst_tm(compare(base, first, normal_bridge), ends[0])
    steps = [compare(p, actual, divided), comp2(p, r, reduce_boundary, padded),
             comp2(p, r, post, missing_unit), compare(p, reference, normal)]
    output = composite(p, r+1, steps)
    assert infer(p, output) == arr(infer(p, actual), actual, normal)
    return p, output


def omit_pole(emitter):
    # Opposed action on a path of two arrows with a moving exterior pole.
    old = tree_ctx(string_tree(0, (1, 1)))
    x, y = maximal_vars(old)
    a, mid, b = src(old, v(x))[1], tgt(old, v(x))[1], tgt(old, v(y))[1]
    full, fc, fh = cylinder(old, set(range(len(old))), 0, True)
    for pole in (a, mid, b):
        marked = {x, y, pole}
        small, caps, changes = cylinder(old, marked, 0, True)
        entries = dict(changes)
        for i in (a, mid, b):
            if i not in marked:
                entries[i] = ident(small, caps[0][i])
        for i in (x, y):
            s, t = src(old, v(i))[1], tgt(old, v(i))[1]
            square = changes[i]
            l = comp2(small, 0, entries[s], caps[1][i])
            u = comp2(small, 0, caps[0][i], entries[t])
            steps = []
            if s not in marked:
                steps.append(compare(small, l, src(small, square)))
            steps.append(square)
            if t not in marked:
                steps.append(compare(small, tgt(small, square), u))
            entries[i] = composite(small, 1, steps)
        sig = label(full, fc, fh, caps, entries, small)
        extended = subst_tm(binary_square(old, full, fc, fh, 0), sig)
        exact = binary_square(old, small, caps, changes, 0)
        steps = []
        if a not in marked:
            steps.append(compare(small, src(small, extended), src(small, exact)))
        steps.append(exact)
        if b not in marked:
            steps.append(compare(small, tgt(small, exact), tgt(small, extended)))
        target = composite(small, 1, steps)
        cell = rc2_full(small, extended, target)
        ty = arr(infer(small, extended), extended, target)
        assert infer(small, cell) == ty
        if emitter and pole == mid:
            start = len(emitter.checks)
            certificate(emitter, small)('omit-exterior-poles', cell, ty)
            scope_checks(emitter, start, 'PartialMask')
    print('Checked three partial masks against the fully marked path at its actual squares.', flush=True)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    out = Emitter() if args.agda else None
    for r in (1, 2, 3):
        for lengths in ((2, 1, 1), (0, 0, 2)):
            p, term = boundary(r, lengths)
            if out and r == 1 and lengths[0] == 2:
                start = len(out.checks)
                certificate(out, p)('boundary-fold', term, infer(p, term))
                scope_checks(out, start, 'BoundarySubstitution')
    print('Checked the smaller target and both promotions in six substitutions of nonvariable labels.', flush=True)
    omit_pole(out)
    if args.agda:
        args.agda.write_text(out.module(args.agda.stem, 'Boundary reduction and insertion of spatial units.'))
