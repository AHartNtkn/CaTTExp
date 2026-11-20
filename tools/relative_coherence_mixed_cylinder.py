"""Check the fixed-object mixed cylinders used to compare raw and biased 3-terms."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from pathlib import Path

from catt import (STAR, arr, chain_tree, check_ctx, coh_between, comp2, disc_tree, infer,
                  maximal_vars, ps_dim, src, sub_from, subst_tm, subst_ty, tdim, tgt,
                  tree_ctx, ucomp, v)
from emit_agda import Emitter
from partial_cylinder_steiner import trees
from relative_coherence_hidden_seam import identity


def sides(ctx, minus, plus, source_changes, target_changes):
    """Positive faces in increasing dimension; objects are fixed."""
    for cut, (s, t) in enumerate(zip(source_changes, target_changes, strict=True), 1):
        minus = comp2(ctx, cut, minus, t)
        plus = comp2(ctx, cut, s, plus)
    assert infer(ctx, minus) == infer(ctx, plus)
    return minus, plus


def change_type(ctx, minus, plus, sources, targets):
    start, end = sides(ctx, minus, plus, sources, targets)
    return arr(infer(ctx, start), start, end)


def changes_on_faces(ty, changes):
    sources, targets = [], []
    while ty[1] != STAR:
        sources.append(changes[ty[2][1]])
        targets.append(changes[ty[3][1]])
        ty = ty[1]
    return sources[::-1], targets[::-1]


@cache
def stationary(d):
    tree = disc_tree(d)
    ctx = tree_ctx(tree)
    top = v(len(ctx) - 1)
    changes = {}
    for i, ty in enumerate(ctx[:-1]):
        if ty != STAR:
            changes[i] = stationary_at(ctx, v(i))
    sources, targets = changes_on_faces(infer(ctx, top), changes)
    left, right = sides(ctx, top, top, sources, targets)
    term = coh_between(ctx, tree, [top], left, right)
    assert infer(ctx, term) == arr(infer(ctx, left), left, right)
    return term


def stationary_at(ctx, term):
    d = tdim(infer(ctx, term)) + 1
    disc = tree_ctx(disc_tree(d))
    return subst_tm(stationary(d), sub_from(disc, ctx, {len(disc)-1: term}))


def check_cylinder(base):
    ctx = ()
    minus, plus, collapse, changes = [], [], [], {}
    for i, ty in enumerate(base):
        if ty == STAR:
            obj = v(len(ctx))
            ctx += (STAR,)
            minus.append(obj)
            plus.append(obj)
            collapse.append(v(i))
            continue
        left, right = v(len(ctx)), v(len(ctx) + 1)
        ctx += (subst_ty(ty, minus), subst_ty(ty, plus))
        minus.append(left)
        plus.append(right)
        sources, targets = changes_on_faces(ty, changes)
        boundary = change_type(ctx, left, right, sources, targets)
        changes[i] = v(len(ctx))
        ctx += (boundary,)
        collapse.extend([v(i), v(i), stationary_at(base, v(i))])
    check_ctx(ctx)
    for i, value in enumerate(collapse):
        assert infer(base, value) == subst_ty(ctx[i], collapse)
    for i in range(len(base)):
        assert subst_tm(minus[i], collapse) == subst_tm(plus[i], collapse) == v(i)
    return len(changes)


def mixed_example(emitter):
    tree = chain_tree(3)
    ctx = tree_ctx(tree)
    slots = [v(i) for i in maximal_vars(ctx)]
    def between(left, right):
        return coh_between(ctx, tree, slots, left, right)
    x, y, z = slots
    f = ucomp(ctx)
    g = comp2(ctx, 0, x, comp2(ctx, 0, y, z))
    normal = comp2(ctx, 0, comp2(ctx, 0, x, y), z)
    assert len({f, g, normal}) == 3
    change_f, change_g = between(f, normal), between(g, normal)
    A = between(f, g)
    B = comp2(ctx, 1, A, identity(ctx, g))
    old = between(A, B)
    new_side = identity(ctx, normal)
    new = identity(ctx, new_side)
    face_changes = [between(*sides(ctx, term, new_side, [change_f], [change_g]))
                    for term in (A, B)]
    left, right = sides(ctx, old, new, [change_f, face_changes[0]], [change_g, face_changes[1]])
    assert left != right
    loop_ctx = (STAR, arr(STAR, v(0), v(0)))
    for name, a, b in (("forward", left, right), ("reverse", right, left)):
        term, ty = between(a, b), arr(infer(ctx, a), a, b)
        assert infer(ctx, term) == ty
        emitter.check_typed(name, ctx, term)
        emitter.check_type(name + "Poles", ctx, term, ty)
        power = v(1)
        for n in range(1, 8):
            images = {i: value for i, value in zip(maximal_vars(ctx), (power, identity(loop_ctx, v(0)), v(1)))}
            sub = sub_from(ctx, loop_ctx, images)
            specialized = subst_tm(term, sub)
            assert infer(loop_ctx, specialized) == subst_ty(ty, sub)
            if n == 3:
                emitter.check_typed(name + "Loop", loop_ctx, specialized)
                emitter.check_type(name + "LoopPoles", loop_ctx, specialized, subst_ty(ty, sub))
            power = comp2(loop_ctx, 0, power, v(1))


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path)
    args = parser.parse_args()
    counts = Counter()
    for size in range(7):
        for tree in trees(size):
            base = tree_ctx(tree)
            if ps_dim(base) <= 3:
                counts["mixed"] += check_cylinder(base)
                counts["arities"] += 1
    print(f"{counts['arities']} arities of height at most three through six tree edges, "
          f"{counts['mixed']} mixed declarations and their collapse labels.")
    emitter = Emitter()
    mixed_example(emitter)
    print("Checked the two directed rank-four changes of parentheses, "
          "including substitutions with an identity slot and loop powers one through seven.")
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, "Mixed cylinders through rank three."))
