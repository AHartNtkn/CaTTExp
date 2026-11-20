"""Check isolated leaf promotions and first-identity comparisons across branches."""
from argparse import ArgumentParser
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, disc_tree, fv_tm, fv_ty, infer, is_ps, maximal_vars,
                  src, sub_from, subst_tm, subst_ty, tdim_tm, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident, susp_ctx, susp_tm
from emit_agda import Emitter
from gray_globe_exterior_actions import certificate, coherence
from gray_globe_sector_terms import arrow
from relative_coherence_cut import Cut


def cylinder(old, marks):
    """Use the signed copies and the successive whiskers at changing poles."""
    ctx = ()
    minus, plus, changes = [], [], {}
    for i, ty in enumerate(old):
        lo = v(len(ctx))
        ctx += (subst_ty(ty, minus),)
        minus.append(lo)
        if i not in marks:
            assert subst_ty(ty, plus) == infer(ctx, lo)
            plus.append(lo)
            continue
        hi = v(len(ctx))
        ctx += (subst_ty(ty, plus),)
        plus.append(hi)
        a, b = lo, hi
        poles = []
        while ty != STAR:
            _, ty, source, target = ty
            poles.append((source[1], target[1]))
        for cut, (source, target) in enumerate(reversed(poles)):
            if target in changes:
                a = comp2(ctx, cut, a, changes[target])
            if source in changes:
                b = comp2(ctx, cut, changes[source], b)
        changes[i] = v(len(ctx))
        ctx += (arrow(ctx, a, b),)
    check_ctx(ctx)
    return ctx, minus, changes


def check_leaf_promotion(k):
    old = tree_ctx(((), disc_tree(k - 1)))
    leaf, top = maximal_vars(old)
    left = src(old, src(old, v(top)))
    right = tgt(old, src(old, v(top)))
    active = {left[1], right[1]}
    for i, ty in enumerate(old):
        if fv_ty(ty) & active:
            active.add(i)
    full, _, changes = cylinder(old, active | {leaf})
    promoted, incl, _ = cylinder(old, {leaf})
    assert is_ps(promoted)
    twice, _, _ = cylinder(promoted, {incl[i][1] for i in active})
    assert full == twice
    nonglobular = [i for i, ty in enumerate(full) if ty != STAR
                   and (ty[2][0] != 'v' or ty[3][0] != 'v')]
    assert nonglobular and min(tdim_tm(full, v(i)) for i in nonglobular) == k
    assert changes[top][1] in nonglobular
    print(f'At head dimension {k}, leaf-first promotion gives the identical typed cylinder.')


def square_comparison():
    path = tree_ctx(((), ()))
    p, q = map(v, maximal_vars(path))
    cap = comp2(path, 0, p, q)
    unit = ident(path, cap)
    k = coherence(path, unit, unit)
    other = comp2(path, 2, k, ident(path, unit))
    comparison = coherence(path, k, other)
    # Complete the square by another path from the same first to last vertex.
    first, last = src(path, p), tgt(path, q)
    corner = v(len(path))
    f, g = v(len(path) + 1), v(len(path) + 2)
    ctx = path + (STAR, arr(STAR, first, corner), arr(STAR, corner, last))
    z = v(len(ctx))
    ctx += (arrow(ctx, cap, comp2(ctx, 0, f, g)),)
    values = tuple(comp2(ctx, 1, t, z) for t in (k, other, comparison))
    a, b, h = values
    assert a != b and infer(ctx, h) == arrow(ctx, a, b)
    assert src(ctx, a) == tgt(ctx, a) == comp2(ctx, 1, unit, z)
    return ctx, values


def schedule(frame, cut, first):
    x, y = map(v, maximal_vars(frame))
    rank = tdim_tm(frame, x) - 1
    left = comp2(frame, cut, x, src(frame, y) if first else tgt(frame, y))
    right = comp2(frame, cut, tgt(frame, x) if first else src(frame, x), y)
    return comp2(frame, rank, left, right) if first else comp2(frame, rank, right, left)


def check(depth, emitter):
    local, original = square_comparison()
    branch, values = local, original
    for _ in range(depth):
        branch = susp_ctx(branch)
        values = tuple(susp_tm(t) for t in values)

    # Glue only the outside pole of each branch. Each top square retains
    # its own two paths and its own local change of path-coherence writing.
    right = (v(1),) + tuple(v(len(branch) + i) for i in range(len(branch) - 1))
    ctx = branch + tuple(subst_ty(ty, right) for ty in branch[1:])
    check_ctx(ctx)
    second = tuple(subst_tm(t, right) for t in values)
    n = depth + 2
    frame = tree_ctx((disc_tree(n), disc_tree(n)))
    x, y = map(v, maximal_vars(frame))
    together = comp2(frame, 0, x, y)
    before, after = schedule(frame, 0, True), schedule(frame, 0, False)

    def evaluate(term, index):
        labels = sub_from(frame, ctx, {x[1]: values[index], y[1]: second[index]})
        return subst_tm(term, labels)

    f, g = evaluate(before, 0), evaluate(after, 1)
    steps = (evaluate(coherence(frame, before, together), 0),
             comp2(ctx, 0, values[2], second[2]),
             evaluate(coherence(frame, together, after), 1))
    h = comp2(ctx, n + 1, comp2(ctx, n + 1, steps[0], steps[1]), steps[2])
    wanted = arrow(ctx, f, g)
    assert f != g and infer(ctx, h) == wanted and tdim_tm(ctx, h) == n + 2
    assert fv_tm(h) >= {len(branch) - 1, len(ctx) - 1}

    # Two different parallel inputs at a repeated outer object have exactly
    # the same projections on both active coordinates, even as raw terms.
    point = (STAR,)
    unit = v(0)
    for _ in range(n):
        unit = ident(point, unit)
    idle = ident(point, unit)
    other_idle = comp2(point, n, idle, idle)
    idle_change = coherence(point, idle, other_idle)
    three = tree_ctx((disc_tree(n),) * 3)
    triple = ucomp(three)
    padded = []
    for pad in (idle, other_idle):
        slots = (pad, values[0], second[0])
        labels = sub_from(three, ctx, dict(zip(maximal_vars(three), slots, strict=True)))
        padded.append(subst_tm(triple, labels))
    larger = tree_ctx((disc_tree(n + 1), disc_tree(n), disc_tree(n)))
    slots = (idle_change, values[0], second[0])
    labels = sub_from(larger, ctx, dict(zip(maximal_vars(larger), slots, strict=True)))
    pad_comparison = subst_tm(ucomp(larger), labels)
    assert padded[0] != padded[1] and infer(ctx, pad_comparison) == arrow(ctx, *padded)

    # Read each actual root cut, then each remaining suspension cut.
    for right_objects, slots in [((1, len(branch)), values), ((len(branch),), second)]:
        cut = Cut(ctx, right_objects)
        for t, expected in zip(slots, original, strict=True):
            decoded, lower = cut.term(t), cut.context()
            for _ in range(depth - 1):
                inner = Cut(lower, (1,))
                decoded, lower = inner.term(decoded), inner.context()
            assert lower == local and decoded == expected
        assert infer(cut.context(), cut.term(h)) == cut.type(wanted)
        assert cut.term(padded[0]) == cut.term(padded[1])
    if emitter:
        certify = certificate(emitter, ctx)
        certify('branch-comparison', h, wanted)
        certify('idle-column-comparison', pad_comparison, arrow(ctx, *padded))
    print(f'At lowest mark {depth}, both projections and the degree-{n + 2} comparison typecheck.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('depth', type=int)
    parser.add_argument('--agda', type=Path)
    options = parser.parse_args()
    if options.depth < 1:
        parser.error('the two branches need at least one suspension')
    output = Emitter() if options.agda else None
    check_leaf_promotion(options.depth + 3)
    check(options.depth, output)
    if output:
        options.agda.write_text(output.module(options.agda.stem, 'Comparisons on two suspended lax squares.'))
