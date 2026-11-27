"""Compare the two coordinate substitutions around pruned insertion squares."""
from argparse import ArgumentParser
from functools import cache
from itertools import product
from pathlib import Path

from catt import STAR, disc_tree, maximal_vars, sub_from, subst_tm, tree_ctx, v
from gray_subdivision_templates import Rows, truncate
from partial_cylinder_steiner import trees
from semistrict_surface_elementary_insertions import exterior as splice_exterior
from semistrict_surface_insertion_clusters import ports
from semistrict_surface_insertion_cut import Assertions, standard, variables
from semistrict_surface_moore_insertion import height
from semistrict_surface_scalar_pairs import trunk


def intervals(dividers):
    ends = (0, *(i for i in range(1, 4) if dividers & (1 << (i - 1))), 4)
    return tuple(zip(ends, ends[1:]))


@cache
def columns(rank, state):
    dividers, prunings = state
    return tuple((a, b, rank - int(all(prunings & (1 << i) for i in range(a, b))))
                 for a, b in intervals(dividers))


@cache
def row(dims):
    return tree_ctx(tuple(disc_tree(k - 1) for k in dims))


@cache
def row_exterior(source, target):
    p = row(tuple(k for _, _, k in source))
    q = row(tuple(k for _, _, k in target))
    if not source:
        assert not target
        return (v(0),)
    q_objects = [v(i) for i, ty in enumerate(q) if ty == STAR]
    images = []
    for a, b, degree in source:
        selected = [j for j, (c, e, _) in enumerate(target) if a <= c and e <= b]
        if selected:
            dims = tuple(target[j][2] for j in selected)
            labels = [v(maximal_vars(q)[j]) for j in selected]
            part = row(dims)
            if len(labels) == 1 and dims[0] == degree:
                images.append(labels[0])
                continue
            embedding = sub_from(part, q, dict(zip(maximal_vars(part), labels, strict=True)))
        else:
            part = row(())
            endpoint = sum(e <= a for _, e, _ in target)
            embedding = (q_objects[endpoint],)
        images.append(subst_tm(standard(part, degree), embedding))
    return sub_from(p, q, dict(zip(maximal_vars(p), images, strict=True)))


def exterior(rank, before, after):
    return row_exterior(columns(rank, before), columns(rank, after))


def check(rank, checks):
    seen = set()
    squares = coordinates = 0
    for dividers, prunings in product(range(8), range(16)):
        start = dividers, prunings
        for i, j in product(range(3), range(4)):
            if dividers & (1 << i) or prunings & (1 << j):
                continue
            end = dividers | (1 << i), prunings | (1 << j)
            q = row(tuple(k for _, _, k in columns(rank, end)))
            direct = exterior(rank, start, end)
            for middle in ((end[0], prunings), (dividers, end[1])):
                first, second = exterior(rank, start, middle), exterior(rank, middle, end)
                for component, expected in zip(first, direct, strict=True):
                    actual = subst_tm(component, second)
                    key = q, actual, expected
                    if actual != expected and key not in seen:
                        checks.equal(q, actual, expected, 'distinct coordinate equations')
                        seen.add(key)
                    coordinates += 1
            squares += 1
    assert seen
    print(f'Rank {rank}: {squares} mixed squares, {coordinates} route coordinates.')


# Three successive lower assignments. The endpoints name occurrences even
# when a letter splits, maps to an identity, or has the same label as another.
lower_words = (
    (((0, 4),), ((4, 8),), ((8, 12),), ((12, 16),)),
    (((0, 2), (2, 4)), (), ((8, 12),), ()),
    (((0, 1), (1, 2), (2, 4)), (), (), ()),
)


@cache
def normal_columns(rank, state):
    dividers, pruned, stage = state
    result = []
    for a, b in intervals(dividers):
        if any(not pruned & (1 << i) for i in range(a, b)):
            result.append((4 * a, 4 * b, rank))
        else:
            for word in lower_words[stage][a:b]:
                result.extend((start, end, rank - 1) for start, end in word)
    return tuple(result)


def normal_exterior(rank, before, after):
    return row_exterior(normal_columns(rank, before), normal_columns(rank, after))


def check_normal_charts(rank, checks):
    seen = set()
    squares = discs = coordinates = 0
    for dividers, pruned, stage in product(range(8), range(16), range(2)):
        start = dividers, pruned, stage
        for d, p in [(1 << i, 0) for i in range(3)] + [(0, 1 << j) for j in range(4)]:
            if dividers & d or pruned & p:
                continue
            end = dividers | d, pruned | p, stage + 1
            target = normal_columns(rank, end)
            q = row(tuple(k for _, _, k in target))
            direct = normal_exterior(rank, start, end)
            for middle in ((end[0], end[1], stage), (dividers, pruned, stage + 1)):
                first = normal_exterior(rank, start, middle)
                second = normal_exterior(rank, middle, end)
                for u, expected in zip(first, direct, strict=True):
                    actual = subst_tm(u, second)
                    key = q, actual, expected
                    if actual != expected and key not in seen:
                        checks.equal(q, actual, expected, 'normalized coordinate equations')
                        seen.add(key)
                    coordinates += 1
            if len(normal_columns(rank, start)) > 1 and len(target) == 1 and target[0][2] == rank:
                discs += 1
            squares += 1
    assert seen and discs
    print(f'Rank {rank}: {squares} lower-change squares, {coordinates} coordinates, '
          f'{discs} transitions from a nonlinear chart to a top disc.')


@cache
def total_quotient(shape):
    return Rows(tree_ctx(shape), height(shape) - 1)


def check_total_quotients(checks):
    shapes = [s for n in range(2, 6) for s in trees(n) if trunk(s) < height(s)]
    unchanged = refined = coordinates = 0
    seen = set()
    for outer in shapes:
        q = total_quotient(outer)
        for path, rank, branch in ports(outer):
            if rank != height(outer):
                continue
            for inner in shapes:
                if height(inner) != rank or trunk(inner) < branch:
                    continue
                address = path[:branch + 1]
                joined, top = splice_exterior(outer, address, inner)
                target = total_quotient(joined)
                if rank - 1 <= trunk(inner):
                    assert q.tree == target.tree
                    lower = variables(q.base)
                    unchanged += 1
                else:
                    result, lower = splice_exterior(q.tree, address, truncate(inner, rank - 1))
                    assert result == target.tree
                    refined += 1
                for u, t in zip(top, q.collapse, strict=True):
                    left, right = subst_tm(u, target.collapse), subst_tm(t, lower)
                    key = target.base, left, right
                    if left != right and key not in seen:
                        checks.equal(target.base, left, right, 'total quotient equations')
                        seen.add(key)
                    coordinates += 1
    assert unchanged and refined and seen
    print(f'Total quotients: {unchanged} unchanged boundaries, {refined} lower splices, '
          f'{coordinates} route coordinates.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('catt_strict', type=Path)
    checks = Assertions()
    for rank in (3, 4):
        check(rank, checks)
        check_normal_charts(rank, checks)
    check_total_quotients(checks)
    checks.run(parser.parse_args().catt_strict.resolve())
