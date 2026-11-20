"""Frame four-dimensional tree expressions by elementary whiskerings and lower-arity heads."""
from argparse import ArgumentParser
from functools import cache
from pathlib import Path

from catt import (arr, comp2, disc_tree, glue_tree, infer, maximal_vars, ps_dim,
                  sub_from, subst_tm, tdim_tm, tree_ctx, ucomp, v)
from emit_agda import Emitter
from partial_cylinder_steiner import trees
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head
from relative_coherence_one_top_slot import carried_pad, lower_face


def align(chart, raw, wanted):
    for degree in range(1, 4):
        for sign in (2, 3):
            before = lower_face(chart, raw, degree, sign)
            after = lower_face(chart, wanted, degree, sign)
            if before == after:
                continue
            if sign == 2:
                raw = comp2(chart, degree, carried_pad(chart, after, before), raw)
            else:
                raw = comp2(chart, degree, raw, carried_pad(chart, before, after))
    assert infer(chart, raw) == infer(chart, wanted)
    return raw


def binary(chart, cut, left, right):
    p, q = (tdim_tm(chart, t) for t in (left, right))
    if max(p, q) < 4 or min(p, q) == cut+1:
        return comp2(chart, cut, left, right)
    small, expr = factored(p, cut, q)
    sigma = sub_from(small, chart, dict(zip(maximal_vars(small), (left, right), strict=True)))
    return subst_tm(expr, sigma)


@cache
def factored(p, cut, q):
    chart = tree_ctx(glue_tree(p, cut, q))
    a, b = map(v, maximal_vars(chart))
    level = min(p, q)-1
    x = binary(chart, cut, a, lower_face(chart, b, level, 2))
    y = binary(chart, cut, lower_face(chart, a, level, 3), b)
    split = comp2(chart, level, x, y)
    return chart, align(chart, split, comp2(chart, cut, a, b))


def suspend(tree, depth):
    for _ in range(depth):
        tree = (tree,)
    return tree


def tree_expression(chart, tree, labels):
    if len(labels) == 1:
        return labels[0]
    depth = 0
    while len(tree) == 1:
        depth += 1
        tree = tree[0]
    left = suspend(tree[:1], depth)
    right = suspend(tree[1:], depth)
    count = len(maximal_vars(tree_ctx(left)))
    a = tree_expression(chart, left, labels[:count])
    b = tree_expression(chart, right, labels[count:])
    return binary(chart, depth, a, b)


@cache
def elementary_heads():
    shapes = set()
    for cut in range(4):
        for p, q in ((4, cut+1), (cut+1, 4)):
            t = ucomp(tree_ctx(glue_tree(p, cut, q)))
            shapes.add((t[1], t[2]))
    return shapes


def inspect(chart, t, seen):
    if t in seen or t[0] == 'v' or tdim_tm(chart, t) < 4:
        return
    seen.add(t)
    _, arity, ty, args = t
    assert ps_dim(arity) <= 3 or (arity, ty) in elementary_heads()
    for value in args:
        inspect(chart, value, seen)


def check(tree, emitter, label):
    chart = tree_ctx(tree)
    slots = list(map(v, maximal_vars(chart)))
    original = ucomp(chart)
    raw = tree_expression(chart, tree, slots)
    reduced = align(chart, raw, original)
    inspect(chart, reduced, set())
    assert top_counts(chart, reduced) == top_counts(chart, original)
    for tag, a, b in (('expand', original, reduced), ('collect', reduced, original)):
        proof = head(chart, a, b)
        ty = arr(infer(chart, a), a, b)
        assert infer(chart, proof) == ty
        if emitter:
            emitter.check_type(tag+label, chart, proof, ty)
    return reduced != original


def run(bound, output):
    emitter = Emitter() if output else None
    for size in range(4, bound+1):
        cases = [tree for tree in trees(size) if ps_dim(tree_ctx(tree)) == 4]
        changed = sum(check(tree, None, '') for tree in cases)
        print(f'{size} edges: {len(cases)} four-arities, {changed} rewritings change syntax.', flush=True)
    shapes = {glue_tree(4, j, p) for p in range(2, 5) for j in range(p-1)}
    shapes |= {glue_tree(p, j, 4) for p in range(2, 5) for j in range(p-1)}
    for i, tree in enumerate(sorted(shapes)):
        assert check(tree, emitter, 'binary'+str(i))
    branching = (disc_tree(3), (), disc_tree(3))
    assert check(branching, emitter, 'branching')
    print(f'{len(shapes)} distinct non-elementary binary arities and one three-branch arity, both directions.')
    if emitter:
        output.write_text(emitter.module(output.stem, 'Elementary four-head reduction at literal faces.'))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('edges', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    run(args.edges, args.agda)
