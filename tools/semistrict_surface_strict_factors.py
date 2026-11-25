"""Read labelled strict pasting diagrams in a globular base and enumerate proper factors."""
from functools import cache, reduce
from itertools import product
from typing import NamedTuple

from catt import disc_tree, maximal_vars, sub_from, tdim_tm, tree_ctx, tree_of
from semistrict_surface_flat_heads import tip_paths


class Diagram(NamedTuple):
    start: int
    steps: tuple


@cache
def height(d):
    return max((1 + height(child) for child, _ in d.steps), default=0)


def join(k, left, right):
    if not k:
        end = left.steps[-1][1] if left.steps else left.start
        if end != right.start:
            raise ValueError('Different horizontal poles')
        return Diagram(left.start, left.steps + right.steps)
    if left.start != right.start or [y for _, y in left.steps] != [y for _, y in right.steps]:
        raise ValueError('Different lower sections')
    return Diagram(left.start, tuple((join(k-1, u, w), y)
                                     for (u, y), (w, _) in zip(left.steps, right.steps)))


@cache
def strict(base, term):
    if term[0] == 'v':
        tree = disc_tree(tdim_tm(base, term))
        shape = tree_ctx(tree)
        labels = sub_from(shape, base, {maximal_vars(shape)[0]: term})
        levels = iter(labels)
        def read(node, start):
            steps = []
            for child in node:
                end, first = next(levels), next(levels)
                steps.append((read(child, first), end[1]))
            return Diagram(start[1], tuple(steps))
        return read(tree, next(levels))
    tree = tree_of(term[1])
    tips = dict(tip_paths(tree))
    def read(node, path):
        if not node:
            return strict(base, term[3][tips[path]])
        return reduce(lambda a, b: join(len(path), a, b),
                      (read(child, (*path, i)) for i, child in enumerate(node)))
    return read(tree, ())


@cache
def splits(d, cut):
    if cut == 0:
        return tuple((Diagram(d.start, d.steps[:i]),
                      Diagram(d.start if i == 0 else d.steps[i-1][1], d.steps[i:]))
                     for i in range(len(d.steps) + 1))
    ends = [y for _, y in d.steps]
    result = []
    for choices in product(*(splits(child, cut-1) for child, _ in d.steps)):
        def half(j):
            return Diagram(d.start, tuple((pair[j], y) for pair, y in zip(choices, ends)))
        result.append((half(0), half(1)))
    return tuple(result)


@cache
def proper_factors(d):
    factors = set()
    for k in range(height(d)):
        for left, right in splits(d, k):
            assert join(k, left, right) == d
            if height(left) > k:
                factors.add(right)
            if height(right) > k:
                factors.add(left)
    return frozenset(factors).union(*(proper_factors(x) for x in factors))
