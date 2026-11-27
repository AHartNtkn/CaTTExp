"""Compare the two coordinate substitutions around pruned insertion squares."""
from argparse import ArgumentParser
from functools import cache
from itertools import product
from pathlib import Path

from catt import disc_tree, maximal_vars, sub_from, subst_tm, tree_ctx, v
from semistrict_surface_insertion_cut import Assertions, standard


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
def exterior(rank, before, after):
    source, target = columns(rank, before), columns(rank, after)
    p = row(tuple(k for _, _, k in source))
    q = row(tuple(k for _, _, k in target))
    tips = maximal_vars(q)
    images = []
    for a, b, degree in source:
        selected = [(k, v(tip)) for (c, e, k), tip in zip(target, tips, strict=True)
                    if a <= c and e <= b]
        dims, labels = zip(*selected, strict=True)
        part = row(dims)
        embedding = sub_from(part, q, dict(zip(maximal_vars(part), labels, strict=True)))
        image = labels[0] if len(labels) == 1 and dims[0] == degree else subst_tm(
            standard(part, degree), embedding)
        images.append(image)
    return sub_from(p, q, dict(zip(maximal_vars(p), images, strict=True)))


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


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('catt_strict', type=Path)
    checks = Assertions()
    for rank in (3, 4):
        check(rank, checks)
    checks.run(parser.parse_args().catt_strict.resolve())
