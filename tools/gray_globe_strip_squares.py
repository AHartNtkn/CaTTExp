"""Compare both orders of growing pure axes on the actual terms of the strips."""
import argparse
from collections import Counter
from functools import cache
from pathlib import Path

from canonical_gray_two_discs import tableau_interpreter
from catt import (comp2, disc_tree, fv_tm, infer, maximal_vars, sub_from, subst_tm,
                  subst_ty, tdim_tm, tree_ctx, v)
from emit_agda import Emitter
from gray_globe_attachments import ordered_factors
from gray_globe_comparison import atom, face
from gray_globe_exterior_actions import arity, certificate, chart_preimage, coherence
from gray_globe_factorizations import orders, profile, rank, truncate
from gray_globe_pure_extension import extend, two_by_two
from gray_globe_section import EMPTY_ROW, cells, row_map
from gray_globe_sector_terms import arrow
from gray_globe_strip_gluing import factors
from gray_globe_three_blocks import endpoints
from gray_path_wedge import compose


def growth(initial, axes):
    shape = [2, 2]
    data = initial
    for axis in axes:
        for bound in (3, 5):
            data = extend(data, tuple(shape), axis, bound, None)
            shape[axis] = bound
    return data


def three_parts(c, last_axis):
    def split(p, axis):
        owner = {site: int(site[axis] <= 2) for site in profile(p) if sum(site) > 2}
        return ordered_factors(p, 2, owner)
    pieces = []
    for p in split(c, last_axis):
        if (1, 2) in profile(p):
            pieces.extend(split(p, 1-last_axis))
        else:
            pieces.append(p)
    assert len(pieces) == 3
    return tuple(pieces)


def strict_pair(a, b):
    height = max(len(a), len(b))
    return compose(a + (EMPTY_ROW,)*(height-len(a)), b + (EMPTY_ROW,)*(height-len(b)), 2)


def minimal_shape(cell):
    sites = profile(cell)
    maxima = tuple(max(p[i] for p in sites) for i in (0, 1))
    return row_map(cell, 0, lambda g: tuple((r, 2 if r == m else tag)
                                           for (r, tag), m in zip(g, maxima)))


def chart_lift(ctx, slots, cut, source, target):
    """Lift these exact terms back to one pasting tree and compare there."""
    heights = tuple(tdim_tm(ctx, t) for t in slots)
    return lift_on(ctx, arity(cut, heights), slots, source, target)


def whisk(ctx, left, fixed, t):
    return comp2(ctx, 2, t, fixed) if left else comp2(ctx, 2, fixed, t)


def then(ctx, *steps):
    result = steps[0]
    for step in steps[1:]:
        result = comp2(ctx, 4, result, step)
    return result


def peel(c, order):
    """Read degree-four singletons in the order prescribed by successive attachments."""
    if len(c[4][0]) == 1:
        return [c]
    site, *rest = order
    owner = {rank(g): int(rank(g)[0] != site) for g in c[4][0]}
    if 0 not in owner.values():
        return peel(c, rest)
    return [w for group in ordered_factors(c, 3, owner) for w in peel(group, rest)]


def exchanges():
    found = set()
    unresolved = 0
    shapes = {False: set(), True: set()}
    for z in endpoints():
        word = peel(z, (0, 1, 4, 3))
        target = peel(z, (4, 3, 0, 1))
        priority = {w[4][0][0]: i for i, w in enumerate(target)}
        needs_mixed = False
        while word != target:
            i = next(i for i in range(len(word)-1)
                     if priority[word[i][4][0][0]] > priority[word[i+1][4][0][0]])
            patch = compose(word[i], word[i+1], 3)
            sites = tuple(sorted(rank(g)[0] for g in patch[4][0]))
            assert sites in ((0, 3), (0, 4), (1, 3), (1, 4))
            needs_mixed |= sites == (1, 3)
            found.add((sites, patch))
            owner = {rank(word[i+j][4][0][0]): 1-j for j in (0, 1)}
            flipped = ordered_factors(patch, 3, owner)
            assert flipped[0][4][0] == word[i+1][4][0]
            word[i:i+2] = flipped
        unresolved += needs_mixed
        shapes[needs_mixed].add(minimal_shape(z))
    assert shapes[True].isdisjoint(shapes[False]) and len(shapes[True]) == len(shapes[False]) == 18
    print(f'{unresolved} labelled endpoints in {len(shapes[True])} shapes require a mixed/mixed exchange')
    return sorted(found)


def check_seams():
    @cache
    def neighbor_order(z):
        sites = {rank(g): rank(g)[0] for g in z[4][0]}
        edges = orders(z, 3, sites)
        return (1, 2) in edges, (2, 3) in edges

    counts = Counter()
    for c in cells((5, 5)):
        sites = profile(c)
        if (3, 3) in sites or not {(2, 3), (3, 2)} <= sites:
            continue
        first, last = factors(c, (3, 3))
        seam = truncate(first, 4, 1)
        assert seam == truncate(last, 4, 0)
        assert neighbor_order(truncate(c, 4, 0)) == (True, True)
        assert neighbor_order(truncate(c, 4, 1)) == (False, False)
        lower_first = (2, 3) in profile(first)
        assert neighbor_order(seam) == (not lower_first, lower_first)
        counts[lower_first] += 1
    print('Four-dimensional seams by first factor:', dict(sorted(counts.items())))


def check(emitter):
    check_seams()
    initial = two_by_two()
    ctx, names, a = growth(initial, (0, 1))
    other, ids, original = growth(initial, (1, 0))
    renaming = tuple(names[g] for g in ids)
    for t, ty in zip(renaming, other):
        assert infer(ctx, t) == subst_ty(ty, renaming)
    b = {c: subst_tm(term, renaming) for c, term in original.items()}
    values = list(map(atom, names))
    jobs = exchanges()
    early = {}

    def parameter(q):
        nonlocal ctx
        if q in early:
            return
        ends = [a[face(q, s)] for s in (0, 1)]
        assert ends == [b[face(q, s)] for s in (0, 1)]
        early[q] = v(len(ctx))
        ctx += (arrow(ctx, *ends),)
        values.append(q)

    def early_factors(w):
        site = rank(w[4][0][0])[0]
        hole = (3, 1) if site == 1 else (1, 3)
        return factors(w, hole)

    for sites, patch in jobs:
        if sites == (0, 4):
            continue
        for direction in (1, -1):
            order = {rank(g): direction*rank(g)[0] for g in patch[4][0]}
            for w in ordered_factors(patch, 3, order):
                if rank(w[4][0][0])[0] in (1, 3):
                    q, = (p for p in early_factors(w) if len(p) == 5)
                    parameter(q)
    evaluate = tableau_interpreter(ctx, values.__getitem__)
    for q, term in early.items():
        assert tuple(map(evaluate, infer(ctx, term)[2:])) == (face(q, 0), face(q, 1))
    certify = certificate(emitter, ctx) if emitter else None
    certified = set()

    @cache
    def presentation(c, first):
        parts = three_parts(c, int(first))
        slots = tuple(a[p] for p in parts)
        assert slots == tuple(b[p] for p in parts)
        i, = (i for i, p in enumerate(parts) if (1, 2) in profile(p))
        return parts, slots, i

    def adjacent(c, first):
        parts, slots, i = presentation(c, first)
        assert i != 1
        j = 0 if i == 2 else 1
        pair = strict_pair(*parts[j:j+2])
        term = comp2(ctx, 2, *slots[j:j+2])
        return pair, term, slots[i], i == 2

    @cache
    def exchange(c, first):
        pair, source, _, _ = adjacent(c, first)
        same_pair, target, _, _ = adjacent(c, not first)
        assert pair == same_pair
        spatial = [a[p] for p in factors(pair, (1, 2))]
        return chart_lift(ctx, spatial, 1, source, target)

    @cache
    def route(c, first):
        """The choices for one 3-state, reused at both ends of every incident square."""
        old, new = (a[c], b[c]) if first else (b[c], a[c])
        parts, slots, _ = presentation(c, first)
        others, other_slots, _ = presentation(c, not first)
        if parts == others:
            return (chart_lift(ctx, slots, 2, old, new),)
        _, raw, middle, left = adjacent(c, first)
        _, changed, same, side = adjacent(c, not first)
        assert middle == same and left == side
        return (chart_lift(ctx, slots, 2, old, whisk(ctx, left, middle, raw)),
                whisk(ctx, left, middle, exchange(c, first)),
                chart_lift(ctx, other_slots, 2, whisk(ctx, left, middle, changed), new))

    def square(c, first):
        old, new = (a[c], b[c]) if first else (b[c], a[c])
        lo, hi = face(c, 0), face(c, 1)
        start, end = route(lo, first), route(hi, first)
        parts, slots, i = presentation(c, first)
        others, other_slots, _ = presentation(c, not first)
        vertical = lambda x, y: comp2(ctx, 3, x, y)
        if parts == others:
            lhs, rhs = vertical(old, end[0]), vertical(start[0], new)
            return chart_lift(ctx, slots, 2, lhs, rhs), lhs, rhs, 'chain'
        pair, raw, middle, left = adjacent(c, first)
        other_pair, changed, same, side = adjacent(c, not first)
        assert pair == other_pair and middle == same and left == side
        m0, m1 = (whisk(ctx, left, middle, r) for r in (raw, changed))
        first_square = chart_lift(ctx, slots, 2, vertical(old, end[0]), vertical(start[0], m0))
        last_square = chart_lift(ctx, other_slots, 2, vertical(m1, end[2]), vertical(start[2], new))
        middle_lhs, middle_rhs = vertical(m0, end[1]), vertical(start[1], m1)
        if len(parts[i]) == 5:
            # The pair is stationary. Exchange its comparison with the middle 4-cell.
            pivot = exchange(lo, first)
            assert pivot == exchange(hi, first)
            args = (pivot, middle) if left else (middle, pivot)
            middle_square = chart_lift(ctx, args, 2, middle_lhs, middle_rhs)
        else:
            # Distribute the stationary whisker, use the two-slot spatial square,
            # then collect the whisker on the other side.
            et, es = exchange(hi, first), exchange(lo, first)
            l, r = vertical(raw, et), vertical(es, changed)
            spatial = [a[p] for p in factors(pair, (1, 2))]
            swap = chart_lift(ctx, spatial, 1, l, r)

            def distribute(x, y, source, target):
                # A vertical string in one slot of a cut-two composition.
                string = ((), ())
                tree = (string, disc_tree(0)) if left else (disc_tree(0), string)
                generic = tree_ctx(((tree,),))
                args = (x, y, middle) if left else (middle, x, y)
                return lift_on(ctx, generic, args, source, target)

            spread = distribute(raw, et, middle_lhs, whisk(ctx, left, middle, l))
            collect = distribute(es, changed, whisk(ctx, left, middle, r), middle_rhs)
            middle_square = then(ctx, spread, whisk(ctx, left, middle, swap), collect)
        proof, lhs, rhs = paste_squares(ctx, old, new, start, end,
                                        (first_square, middle_square, last_square))
        return proof, lhs, rhs, 'fork'

    counts = Counter()
    shapes = set()
    for c in sorted(a):
        if len(c) != 5 or len(c[4][0]) != 1 or len(c[3][0]) != 4:
            continue
        site = rank(c[4][0][0])[0]
        shapes.add(minimal_shape(c))
        for first in (True, False):
            proof, lhs, rhs, kind = square(c, first)
            ty = infer(ctx, proof)
            assert ty[2:] == (lhs, rhs)
            assert evaluate(lhs) == evaluate(rhs) == c and evaluate(proof) == c + (EMPTY_ROW,)
            counts[site, kind] += 1
            if certify and (site, kind) not in certified:
                certify(f'site-{site}-{kind}', proof, ty)
                certified.add((site, kind))
    print(f'{len(shapes)} minimal face shapes; directed squares by site and order: {dict(sorted(counts.items()))}')

    swaps = Counter()
    remaining = set()
    mixed_patches = 0
    parameters = {t[1] for t in early.values()}

    def bridge(s, forward):
        changes = route(s, forward)
        term = changes[0]
        for change in changes[1:]:
            term = comp2(ctx, 3, term, change)
        return term

    def early_term(w, chosen):
        slots = [early[p] if p in early else chosen[p] for p in early_factors(w)]
        return comp2(ctx, 2, *slots)

    for sites, patch in jobs:
        chosen = b if sites == (1, 4) else a
        if sites == (0, 4):
            slots = presentation(patch, True)[1]
        elif sites != (1, 3):
            hole = (1, 3) if sites == (0, 3) else (3, 1)
            slots = [early[p] if p in early else chosen[p] for p in factors(patch, hole)]
        routes = []
        for direction in (1, -1):
            precedence = {rank(g): direction*rank(g)[0] for g in patch[4][0]}
            steps = []
            for w in ordered_factors(patch, 3, precedence):
                if sites == (1, 3) and rank(w[4][0][0])[0] == 1:
                    term = early_term(w, b)
                    term = comp2(ctx, 3, bridge(face(w, 0), True), term)
                    steps.append(comp2(ctx, 3, term, bridge(face(w, 1), False)))
                elif w in chosen:
                    steps.append(chosen[w])
                else:
                    steps.append(early_term(w, chosen))
            routes.append(comp2(ctx, 3, *steps))
        if sites == (1, 3):
            shape = minimal_shape(patch)
            expected = arrow(ctx, a[face(patch, 0)], a[face(patch, 1)])
            used = [parameters & fv_tm(t) for t in routes]
            assert all(len(group) == 2 for group in used) and used[0].isdisjoint(used[1])
            for i, term in enumerate(routes):
                assert infer(ctx, term) == expected and evaluate(term) == patch
                if certify and shape not in remaining:
                    tag = shape[4][0][0][0][1]
                    certify(f'remaining-{tag}-route-{i}', term, expected)
            remaining.add(shape)
            mixed_patches += 1
            continue
        for src, tgt in (routes, routes[::-1]):
            proof = chart_lift(ctx, slots, 2, src, tgt)
            ty = arrow(ctx, src, tgt)
            assert infer(ctx, proof) == ty and evaluate(proof) == patch + (EMPTY_ROW,)
            assert evaluate(src) == evaluate(tgt) == patch
            if certify and not swaps[sites]:
                certify(f'exchange-{sites[0]}-{sites[1]}', proof, ty)
            swaps[sites] += 1
    print(f'{len(early)} early mixed parameters; directed exchanges: {dict(sorted(swaps.items()))}')
    assert len(remaining) == 2 and {p[4][0] for p in remaining} == {
        (((1, side), (3, 2)), ((3, 2), (1, side))) for side in (0, 1)}
    print(f'{mixed_patches} remaining mixed patches in {len(remaining)} face shapes')


def lift_on(ctx, generic, args, source, target):
    sigma = sub_from(generic, ctx, dict(zip(maximal_vars(generic), args, strict=True)))
    recover = chart_preimage(generic, sigma)
    l, r = recover(source), recover(target)
    assert l is not None and r is not None
    head = coherence(generic, l, r)
    assert infer(generic, head) == head[2]
    return subst_tm(head, sigma)


def paste_squares(ctx, old, new, start, end, squares):
    """Move across a length-three path one square at a time."""
    def vertical(x, y):
        return comp2(ctx, 3, x, y)

    current = vertical(old, vertical(vertical(end[0], end[1]), end[2]))
    initial = current
    proofs = []

    def rebracket(items, target):
        nonlocal current
        if current != target:
            proofs.append(chart_lift(ctx, items, 3, current, target))
            current = target

    for i, sq in enumerate(squares):
        s, t = infer(ctx, sq)[2:]
        step = sq
        for pre in reversed(start[:i]):
            s, t, step = (vertical(pre, x) for x in (s, t, step))
        for post in end[i+1:]:
            s, t, step = (vertical(x, post) for x in (s, t, step))
        before_slot = infer(ctx, squares[i])[2]
        binary = maximal_vars(before_slot[1])
        before, after = [before_slot[3][j] for j in binary]
        rebracket(start[:i] + (before, after) + end[i+1:], s)
        proofs.append(step)
        current = t
    goal = vertical(vertical(vertical(start[0], start[1]), start[2]), new)
    rebracket(start + (new,), goal)
    return then(ctx, *proofs), initial, goal


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    check(emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Actual boundary squares for the two strips.'))
