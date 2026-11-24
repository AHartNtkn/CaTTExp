"""Factor tree insertions, check their typed exterior maps, and test the width bound."""
import argparse
from collections import Counter
from functools import cache
from itertools import product
from pathlib import Path

from catt import (disc_tree, glue_tree, infer, ps_boundary_vars, restrict, sub_from,
                  subst_tm, subst_ty, tree_ctx, tree_of, ucomp, v)
from ct_suspension import ident
from partial_cylinder_steiner import trees
from semistrict_surface_insertion_cut import Assertions, standard, variables
from semistrict_surface_moore_insertion import height
from semistrict_surface_peak_sections import columns
from semistrict_surface_scalar_pairs import branches, positions, splice, trunk
from semistrict_surface_unital_reassociation import check_rice


def subtree(tree, path):
    for index in path:
        tree = tree[index]
    return tree


@cache
def slots(tree):
    return {p: cell for p, (cell, stop) in columns(tree).items() if cell+1 == stop}


def port(tree, parent, i):
    """The cell at the i-th seam of the given list of children."""
    chart = columns(tree)
    if i:
        return v(chart[parent + (i-1,)][0]-1)
    return v(chart[parent][0] if parent else 0)


def exterior(tree, path, inner):
    """The one-step exterior with only unary disc and endo heads simplified."""
    h = len(path)-1
    rank = len(path) + height(subtree(tree, path))
    joined = splice(tree, path, inner)
    out, inside, result = map(tree_ctx, (tree, inner, joined))
    window = subtree(inner, (0,)*h)
    parent, first = path[:-1], path[-1]
    entry = port(joined, parent, first)
    if window:
        labels = {slot: v(slots(joined)[parent + (first+p[h],) + p[h+1:]])
                  for p, slot in slots(inner).items()}
        entry = subst_tm(ucomp(inside), sub_from(inside, result, labels))
    for _ in range(rank - height(inner)):
        entry = ident(result, entry)
    active = path + (0,)*(rank-len(path))
    top = {}
    for old, slot in slots(tree).items():
        if old == active:
            top[slot] = entry
        else:
            p = old
            if old[:h] == parent and old[h] > first:
                p = parent + (old[h] + len(window)-1,) + old[h+1:]
            top[slot] = v(slots(joined)[p])
    sigma = sub_from(out, result, top)
    assert all(infer(result, t) == subst_ty(ty, sigma) for t, ty in zip(sigma, out, strict=True))
    return joined, sigma


def steps(path, rank, inner):
    """Yield (address, inserted tree); each step prunes one leaf or doubles a disc."""
    d, h = height(inner), len(path)-1
    for old_rank in range(rank, d, -1):
        yield path + (0,)*(old_rank-len(path)), disc_tree(old_rank-1)
    if d == trunk(inner):
        return

    def grow(parent, first, wanted):
        j = len(parent)
        for extra in range(len(wanted)-1):
            yield parent + (first+extra,), glue_tree(d, j, d)
        for i, child in enumerate(wanted):
            if child:
                yield from grow(parent + (first+i,), 0, child)

    yield from grow(path[:-1], path[-1], subtree(inner, (0,)*h))
    for leaf in slots(inner):
        local = path[:-1] + (path[-1]+leaf[h],) + leaf[h+1:]
        for old_rank in range(d, len(leaf), -1):
            yield local + (0,)*(old_rank-len(leaf)), disc_tree(old_rank-1)


def blocks(tree, rank, level, labels):
    """Evaluate a rank-n head by grouping labels at the given depth."""
    values = []
    for prefix in positions(tree, level):
        block = tuple(atom for suffix in positions(subtree(tree, prefix), rank-level)
                      for atom in labels[prefix+suffix])
        if block:
            values.append(block)
    if not values:
        return ()
    if len(values) == 1:
        return values[0]
    return (('node', tuple(values)),)


@cache
def check_signed_rows(tree, path, inner):
    """Compare the two routes on every coordinate of each signed boundary."""
    joined, sigma = exterior(tree, path, inner)
    rank = len(path) + height(subtree(tree, path))
    cut = len(path)-1
    for s in range(height(tree)+1):
        for sign in ('-', '+'):
            old, new = tree_ctx(tree), tree_ctx(joined)
            before, inc = restrict(old, ps_boundary_vars(old, s, sign))
            after, inc_new = restrict(new, ps_boundary_vars(new, s, sign))
            if s < rank and (s <= cut or height(inner) < rank):
                assert before == after
                face = variables(before)
            else:
                reduced = inner
                if s < rank:
                    reduced = glue_tree(s, cut, s)
                target, face = exterior(tree_of(before), path, reduced)
                assert tree_ctx(target) == after
            assert tuple(subst_tm(t, sigma) for t in inc) == tuple(
                subst_tm(t, inc_new) for t in face)
    return 2*(height(tree)+1)


def check_shapes(limit, rice):
    shapes = [tree for size in range(limit+1) for tree in trees(size)]
    counts = Counter()
    checked = set()
    for tree in shapes:
        for path, rank in branches(tree):
            for inner in shapes:
                if height(inner) > rank or trunk(inner) < len(path)-1:
                    continue
                wanted, direct = exterior(tree, path, inner)
                result, current = tree, variables(tree_ctx(tree))
                split_count = 0
                for address, pair in steps(path, rank, inner):
                    counts['signed row squares'] += check_signed_rows(result, address, pair)
                    if height(pair) > trunk(pair):
                        width = height(pair)-len(address)+1
                        assert width <= height(inner)-trunk(inner)
                        split_count += 1
                    result, change = exterior(result, address, pair)
                    current = tuple(subst_tm(t, change) for t in current)
                assert result == wanted
                assert split_count == max(len(slots(inner))-1, 0)
                counts['legal insertions'] += 1
                ctx = tree_ctx(wanted)
                for a, b in zip(direct, current, strict=True):
                    if a != b and (ctx, a, b) not in checked:
                        rice.equal(ctx, a, b, 'exterior entries after factorization')
                        checked.add((ctx, a, b))
                # Compare the standard outer head at full rank under both maps;
                # the reindexed bound types can differ as raw expressions.
                if direct != current:
                    head = standard(tree_ctx(tree), height(tree))
                    left = subst_tm(head, direct)
                    right = subst_tm(head, current)
                    if (ctx, left, right) not in checked:
                        rice.equal(ctx, left, right, 'outer heads at reindexed types')
                        checked.add((ctx, left, right))
    return counts


def check_width(limit, rice, binary):
    checked = 0
    for n in range(1, 6):
        for level in range(1, n+1):
            cut = level-1
            inner = glue_tree(n, cut, n)
            path = (0,)*(cut+1)
            joined, sigma = exterior(inner, path, inner)
            triple = tree_ctx(joined)
            pair = tree_ctx(inner)
            head = standard(pair, n)
            nested = subst_tm(head, sigma)
            joined_head = ('coh', triple, subst_ty(head[2], sigma), variables(triple))
            assert infer(triple, nested) == infer(triple, joined_head)
            rice.equal(triple, nested, joined_head, 'new parallel head equation')
            if binary and level == n:
                negative = Assertions()
                negative.equal(triple, nested, joined_head, 'strict units separator')
                check_rice(negative, binary, '--su', positive=False)
            abc = {p: ('a',) for p in positions(joined, n)}
            double = {p: ('a',) for p in positions(inner, n)}
            nested_labels = dict(double)
            nested_labels[min(double)] = blocks(inner, n, level, double)
            assert blocks(joined, n, level, abc) != blocks(inner, n, level, nested_labels)

    for size in range(1, limit+1):
        for tree in trees(size):
            n = height(tree)
            for level in range(1, n+1):
                for path, rank in branches(tree):
                    cut = len(path)-1
                    if rank-cut > n-level:
                        continue
                    pair = glue_tree(rank, cut, rank)
                    joined = splice(tree, path, pair)
                    peaks = positions(joined, n)
                    for occupied in product((False, True), repeat=len(peaks)):
                        labels = {p: (i,) if bit else () for i, (p, bit) in
                                  enumerate(zip(peaks, occupied, strict=True))}
                        lower = {}
                        for p in positions(tree, n):
                            if p[:cut+1] == path:
                                second = path[:-1] + (path[-1]+1,) + p[cut+1:]
                                lower[p] = labels[p] + labels[second]
                            else:
                                q = p
                                if p[:cut] == path[:-1] and p[cut] > path[-1]:
                                    q = p[:cut] + (p[cut]+1,) + p[cut+1:]
                                lower[p] = labels[q]
                        assert blocks(tree, n, level, lower) == blocks(joined, n, level, labels)
                        checked += 1
    return checked


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--edges', type=int, default=5)
    parser.add_argument('--rice-binary', type=Path)
    args = parser.parse_args()
    checks = Assertions()
    print(dict(check_shapes(args.edges, checks)))
    binary = args.rice_binary.resolve() if args.rice_binary else None
    print(f'{check_width(args.edges, checks, binary)} occupied-slot comparisons')
    print(dict(checks.count))
    if binary:
        check_rice(checks, binary, '--sua')
