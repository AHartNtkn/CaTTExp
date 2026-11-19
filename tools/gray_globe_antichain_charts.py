"""Verify all local serializations from the common lower cut in a globe pair."""
import argparse
from collections import Counter
from itertools import permutations

from gray_globe_attachments import ordered_factors
from gray_globe_factorizations import components, orders, profile, truncate
from gray_globe_section import EMPTY_ROW, cells
from gray_path_wedge import compose


def paste(x, y, cut):
    assert x[:cut] == y[:cut] and x[cut][1] == y[cut][0]
    height = max(len(x), len(y))
    return compose(x + (EMPTY_ROW,)*(height-len(x)), y + (EMPTY_ROW,)*(height-len(y)), cut)


def check_embedding(pieces, cut):
    """Evaluate every intrinsic cell of the string of globes and detect collisions."""
    values = set()

    def record(value):
        assert value not in values
        values.add(value)

    for degree in range(cut):
        for side in (0, 1):
            record(truncate(pieces[0], degree, side))
    record(truncate(pieces[0], cut, 0))
    for piece in pieces:
        record(truncate(piece, cut, 1))

    for start in range(len(pieces)):
        prefixes = [None]
        for piece in pieces[start:]:
            choices = [truncate(piece, degree, side)
                       for degree in range(cut+1, len(piece)-1) for side in (0, 1)]
            choices.append(piece)
            prefixes = [end if prefix is None else paste(prefix, end, cut)
                        for prefix in prefixes for end in choices]
            for value in prefixes:
                record(value)
    return len(values)


def check(m, n):
    sizes = Counter()
    orders_checked = 0
    chart_cells = 0
    for c in cells((m, n)) - {()}:
        sites = profile(c)
        for cut in range(1, len(c)-1):
            upper = components(sites, cut)
            if len(upper) < 2:
                continue
            owner = {p: i for i, group in enumerate(upper) for p in group}
            if orders(c, cut, owner):
                continue
            lower = components(sites, cut-1)
            parent = {p: i for i, group in enumerate(lower) for p in group}
            parents = [{parent[p] for p in group} for group in upper]
            assert all(len(group) == 1 for group in parents)
            assert len(set.union(*parents)) == len(upper)
            pieces = ordered_factors(c, cut-1, parent)
            chart_cells += check_embedding(pieces, cut-1)
            moving = {i: owner[next(p for p in profile(t) if sum(p) > cut)]
                      for i, t in enumerate(pieces) if len(t) > cut+1}
            sizes[len(upper)] += 1
            for order in permutations(range(len(upper))):
                expected = ordered_factors(c, cut, {p: order.index(i) for p, i in owner.items()})
                done = set()
                result = None
                for group, wanted in zip(order, expected):
                    args = [truncate(t, cut, int(moving[i] in done)) if i in moving and moving[i] != group else t
                            for i, t in enumerate(pieces)]
                    step = args[0]
                    for other in args[1:]:
                        step = paste(step, other, cut-1)
                    assert step == wanted
                    done.add(group)
                    result = step if result is None else paste(result, step, cut)
                assert result == c
                orders_checked += 1
    print(f'D^{m} tensor D^{n}: {dict(sorted(sizes.items()))} cells/cuts by antichain size, '
          f'{orders_checked} complete serializations, {chart_cells} chart cells checked for injectivity')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    args = parser.parse_args()
    if min(args.m, args.n) < 0:
        parser.error('globe dimensions must be nonnegative')
    check(args.m, args.n)
