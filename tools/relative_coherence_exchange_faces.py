"""Check CaTT representatives for the two types of 2-face in a 3-cell fibre."""

import sys
from functools import reduce
from itertools import permutations, product

from catt import (
    arr, comp2, comp_tree, disc_tree, glue_tree, infer, maximal_vars, sub_from,
    subst_tm, tdim_tm, tree_ctx, v,
)
from emit_agda import Emitter


def string_tree(cut, dimensions):
    tree = tuple(disc_tree(dim - cut - 1) for dim in dimensions)
    for _ in range(cut):
        tree = (tree,)
    return tree


def composite(context, cut, terms):
    return reduce(lambda a, b: comp2(context, cut, a, b), terms)


def head(context, start, end):
    assert infer(context, start) == infer(context, end)
    ty = arr(infer(context, start), start, end)
    result = ('coh', context, ty, tuple(map(v, range(len(context)))))
    assert infer(context, result) == ty
    return result


def compose_rows(context, rows):
    return comp_tree(string_tree(1, [tdim_tm(context, t) for t in rows]), context, rows)


def steps(context, rows, order):
    state = [infer(context, t)[2] if tdim_tm(context, t) == 3 else t for t in rows]
    result = []
    for i in order:
        state[i] = rows[i]
        result.append(compose_rows(context, state))
        state[i] = infer(context, rows[i])[3]
    return result


def reassociate(context, three, to_left):
    paste = tree_ctx(string_tree(2, [3, 3, 3]))
    x, y, z = map(v, maximal_vars(paste))
    left = comp2(paste, 2, comp2(paste, 2, x, y), z)
    right = comp2(paste, 2, x, comp2(paste, 2, y, z))
    comparison = head(paste, right, left) if to_left else head(paste, left, right)
    assignment = sub_from(paste, context, dict(zip(maximal_vars(paste), three)))
    return subst_tm(comparison, assignment)


def hexagon():
    paste = tree_ctx(string_tree(1, [3, 3, 3]))
    rows = list(map(v, maximal_vars(paste)))

    def exchange(order, pos):
        # At a facet the third row is fixed at its source or target.
        pair = order[pos:pos+2]
        fixed = order[2] if pos == 0 else order[0]
        chosen_face = infer(paste, rows[fixed])[2 if pos == 0 else 3]
        small = tree_ctx(string_tree(1, [2 if i == fixed else 3 for i in range(3)]))
        small_rows = list(map(v, maximal_vars(small)))
        first = composite(small, 2, steps(small, small_rows, pair))
        last = composite(small, 2, steps(small, small_rows, pair[::-1]))
        frame_rows = [chosen_face if i == fixed else r for i, r in enumerate(rows)]
        sigma = sub_from(small, paste, dict(zip(maximal_vars(small), frame_rows)))
        local = subst_tm(head(small, first, last), sigma)
        old = steps(paste, rows, order)
        new_order = list(order)
        new_order[pos:pos+2] = pair[::-1]
        new = steps(paste, rows, new_order)
        if pos == 0:
            result = comp2(paste, 2, local, old[2])
        else:
            result = composite(paste, 3, [reassociate(paste, old, False),
                                          comp2(paste, 2, old[0], local),
                                          reassociate(paste, new, True)])
        assert infer(paste, result)[2:] == (composite(paste, 2, old), composite(paste, 2, new))
        return new_order, result

    def route(swaps):
        order = [0, 1, 2]
        path = []
        for i in swaps:
            order, change = exchange(order, i)
            path.append(change)
        assert order == [2, 1, 0]
        return composite(paste, 3, path)

    cell = head(paste, route((0, 1, 0)), route((1, 0, 1)))
    return paste, cell


def square():
    paste = tree_ctx(glue_tree(4, 2, 4))
    a, b = map(v, maximal_vars(paste))
    a0, a1 = infer(paste, a)[2:]
    b0, b1 = infer(paste, b)[2:]
    ab = comp2(paste, 3, comp2(paste, 2, a, b0), comp2(paste, 2, a1, b))
    ba = comp2(paste, 3, comp2(paste, 2, a0, b), comp2(paste, 2, a, b1))
    return paste, head(paste, ab, ba)


def check_facets(n):
    # The extreme hom of the rigidified n-cube is the cone on the chains
    # of the proper Boolean lattice. A cut S splits a facet into two factors.
    sets = range(1, (1 << n) - 1)
    def chains_after(lower):
        yield ()
        for upper in sets:
            if lower != upper and lower & upper == lower:
                for tail in chains_after(upper):
                    yield (upper,) + tail
    chains = set(chains_after(0))
    for cut in sets:
        facet = {chain for chain in chains if cut in chain}
        pieces = {(c[:c.index(cut)], c[c.index(cut)+1:]) for c in facet}
        assert len(pieces) == len({p for p, _ in pieces}) * len({q for _, q in pieces})
    maximal = {c for c in chains if len(c) == n-1}
    assert len(maximal) == len(list(permutations(range(n))))
    if n == 3:
        assert len(maximal) == 6 and len(list(sets)) == 6


def check_interval_orders(width):
    # For a directed triangle, enumerate the locally consistent weak
    # comparisons on each lane and collect the possible strict witnesses.
    cycle = [(0, 1), (1, 2), (2, 0)]
    local_signs = {}
    for mask in range(8):
        present = [i for i in range(3) if mask & (1 << i)]
        witnesses = set()
        for ranks in product(range(3), repeat=len(present)):
            rank = dict(zip(present, ranks))
            edges = [(i, a, b) for i, (a, b) in enumerate(cycle) if a in rank and b in rank]
            if all(rank[a] <= rank[b] for _, a, b in edges):
                witnesses.add(sum(1 << i for i, a, b in edges if rank[a] < rank[b]))
        local_signs[mask] = witnesses

    def admits_cycle(lanes):
        possible = {0}
        for mask in lanes:
            possible = {seen | current for seen in possible for current in local_signs[mask]}
        return 7 in possible

    intervals = [(left, right) for right in range(width) for left in range(right+1)]
    for triple in product(intervals, repeat=3):
        lanes = (sum(1 << i for i, (left, right) in enumerate(triple) if left <= j <= right)
                 for j in range(width))
        assert not admits_cycle(lanes)
    # Without consecutive supports, the three strict comparisons can coexist.
    assert admits_cycle([0b011, 0b110, 0b101])
    return len(intervals) ** 3


if __name__ == '__main__':
    witnesses = [(name, *fn()) for name, fn in [('square', square), ('hexagon', hexagon)]]
    for n in range(2, 7):
        check_facets(n)
    triples = check_interval_orders(6)
    if sys.argv[1:] == ['--agda']:
        out = Emitter()
        for name, context, term in witnesses:
            out.check_typed(name, context, term)
        print(out.module('ExchangeFaces', 'Square and hexagon with the prescribed boundary paths.'))
    else:
        assert not sys.argv[1:]
        print('Square and hexagon 5-terms checked, including all six whiskered hexagon edges.')
        print('Boolean chain facets checked through the six-cube.')
        print(f'Weak comparisons tested for {triples} ordered interval triples.')
