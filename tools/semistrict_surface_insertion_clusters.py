"""Check connected, positive insertion overlaps at their transported generic types."""
from argparse import ArgumentParser
from dataclasses import dataclass
from functools import cache
from itertools import combinations, permutations
from pathlib import Path

from catt import STAR, arr, comp2, disc_tree, infer, maximal_vars, sub_from, subst_tm, subst_ty, tree_ctx, v
from emit_agda import Emitter
from partial_cylinder_steiner import trees
from relative_coherence_exchange_faces import head
from semistrict_surface_grid_tracks import associator, temporal
from semistrict_surface_insertion_cut import Assertions
from semistrict_surface_moore_insertion import height
from semistrict_surface_scalar_pairs import branches, splice, trunk


@dataclass(frozen=True)
class Node:
    cut: int
    left: object
    right: object
    mark: int = 0


def joined(left, right, cut):
    if cut == 0:
        return left + right
    assert len(left) == len(right) == 1
    return (joined(left[0], right[0], cut - 1),)


def joined_shape(tree, rank):
    if not isinstance(tree, Node):
        return disc_tree(rank)
    return joined(joined_shape(tree.left, rank), joined_shape(tree.right, rank), tree.cut)


def frontier(pattern):
    if isinstance(pattern, Node):
        return frontier(pattern.left) + frontier(pattern.right)
    return [pattern]


def reading(ctx, tree, labels):
    if not isinstance(tree, Node):
        return labels[tree]
    return comp2(ctx, tree.cut, reading(ctx, tree.left, labels),
                 reading(ctx, tree.right, labels))


def component(tree, marks, children):
    """The edge to an uncontracted subtree is a slot in this corolla."""
    def slot(child):
        if isinstance(child, Node) and marks & child.mark:
            return component(child, marks, children)
        children.append(child)
        return len(children) - 1
    return Node(tree.cut, slot(tree.left), slot(tree.right))


@cache
def ports(shape):
    """List all leaves in planar order with dimension and least branch height."""
    minimum = {}
    for path, dim in branches(shape):
        leaf = path + (0,) * (dim - len(path))
        minimum[leaf] = min(minimum.get(leaf, dim), len(path) - 1)
    return tuple((p, len(p), h) for p, h in sorted(minimum.items()))


def check_residuals():
    shapes = [s for size in range(2, 7) for s in trees(size) if trunk(s) < height(s)]
    count = 0
    for outer in shapes:
        for i, (p, dim, branch) in enumerate(ports(outer)):
            if dim != height(outer):
                continue
            for inner in shapes:
                if height(inner) != dim or trunk(inner) < branch:
                    continue
                result = splice(outer, p[:branch + 1], inner)
                before = [port[1:] for port in ports(outer)]
                before[i:i + 1] = [port[1:] for port in ports(inner)]
                assert before == [port[1:] for port in ports(result)]
                assert trunk(outer) == trunk(result)
                count += 1
    print(f'{count} positive splices preserve trunk and the ordered residual branch heights.')


def check(rank, emitter, rice):
    # The middle corolla has both a nested and a sibling overlap. Each cut
    # meets the trunk condition of the head inserted into its argument.
    tree = Node(0, Node(1, Node(rank - 1, 0, 1, 4), 2, 1),
                Node(rank - 1, 3, 4, 2))
    ctx = tree_ctx(joined_shape(tree, rank))
    args = dict(zip(frontier(tree), map(v, maximal_vars(ctx)), strict=True))

    def evaluate(node, marks):
        if not isinstance(node, Node):
            return args[node]
        subs = []
        pattern = component(node, marks, subs)
        arity = tree_ctx(joined_shape(pattern, rank))
        ports = maximal_vars(arity)
        old = reading(arity, pattern, dict(zip(frontier(pattern), map(v, ports), strict=True)))
        labels = [evaluate(child, marks) for child in subs]
        return ('coh', arity, infer(arity, old),
                sub_from(arity, ctx, dict(zip(ports, labels, strict=True))))

    vertices = tuple(evaluate(tree, mask) for mask in range(8))
    original = reading(ctx, tree, args)
    assert all(infer(ctx, cell) == infer(ctx, original) for cell in vertices)
    assert vertices[0] == original and len(set(vertices)) == 8
    if rice:
        for cell in vertices:
            rice.equal(ctx, original, cell, 'positive insertion readings')

    @cache
    def realize(flag):
        def face(*indices):
            return realize(tuple(flag[i] for i in indices))
        if len(flag) == 1:
            return vertices[flag[0]]
        if len(flag) == 2:
            return head(ctx, face(0), face(1))
        if len(flag) == 3:
            return head(ctx, face(0, 2), temporal(ctx, face(0, 1), face(1, 2)))
        a, b, c = face(0, 1), face(1, 2), face(2, 3)
        left = temporal(ctx, face(0, 2, 3), comp2(ctx, rank, face(0, 1, 2), c))
        left = temporal(ctx, left, associator(ctx, a, b, c))
        right = temporal(ctx, face(0, 1, 3), comp2(ctx, rank, a, face(1, 2, 3)))
        return head(ctx, left, right)

    flags = set()
    for order in permutations((1, 2, 4)):
        chain = (0, order[0], order[0] | order[1], 7)
        for n in range(1, 5):
            flags.update(combinations(chain, n))
    assert len(flags) == 51
    # Fold the five different generic top variables to the same loop over
    # a composite lower edge. Every face is then specialized by the same map.
    folded = (STAR, arr(STAR, v(0), v(0)))
    pole = comp2(folded, 0, v(1), v(1))
    for _ in range(2, rank + 1):
        folded += (arr(infer(folded, pole), pole, pole),)
        pole = v(len(folded) - 1)
    change = sub_from(ctx, folded, dict.fromkeys(maximal_vars(ctx), pole))
    for i, flag in enumerate(sorted(flags)):
        term = realize(flag)
        value = subst_tm(term, change)
        expected = subst_ty(infer(ctx, term), change)
        assert infer(folded, value) == expected
        if emitter and len(flag) == 4:
            emitter.check_type('flag' + str(i), folded, value, expected)
    print(f'Rank {rank}: 8 distinct readings, all 51 flags at their folded faces.')


if __name__ == '__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('--agda-dir', type=Path)
    p.add_argument('--catt-strict', type=Path)
    opts = p.parse_args()
    if opts.agda_dir:
        opts.agda_dir.mkdir(parents=True, exist_ok=True)
    check_residuals()
    rice = Assertions() if opts.catt_strict else None
    for rank in (3, 4):
        emitter = Emitter() if opts.agda_dir else None
        check(rank, emitter, rice)
        if emitter:
            name = 'InsertionCluster' + str(rank)
            (opts.agda_dir / (name + '.agda')).write_text(emitter.module(name, __doc__))
    if rice:
        rice.run(opts.catt_strict)
