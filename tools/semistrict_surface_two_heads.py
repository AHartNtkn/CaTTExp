"""Find two ordinary heads sharing an unspecified literal middle face."""

import argparse
from functools import cache
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, TypeError_, arr, comp2, disc_tree, fv_tm, fv_ty, infer,
                  maximal_vars, mk_coh, sub_from, subst_tm, tdim_tm, tree_ctx, tree_of, v)
from semistrict_surface_flat_heads import (assemble, charts, check_weak, flat_head,
                                           inverse_substitution, routes, seam, tip_paths, trees_with_leaves)
from semistrict_surface_insertion_cut import variables
from semistrict_surface_rank_cut import RankCut


def join(cut, left, right):
    if cut == 0:
        return left + right
    if len(left) != len(right):
        raise ValueError('Incompatible strict sections')
    return tuple(join(cut - 1, x, y) for x, y in zip(left, right))


@cache
def chart_trees(ctx, term):
    """Possible full diagrams when subexpressions may be labelled as atoms."""
    shapes = {disc_tree(tdim_tm(ctx, term))}
    if term[0] == 'v':
        return shapes
    _, arity, _, labels = term
    tree = tree_of(arity)
    tips = dict(tip_paths(tree))

    def expand(node, path):
        if not node:
            return chart_trees(ctx, labels[tips[path]])
        it = iter(enumerate(node))
        j, child = next(it)
        found = expand(child, (*path, j))
        for j, child in it:
            next_shapes = set()
            for a, b in product(found, expand(child, (*path, j))):
                try:
                    next_shapes.add(join(len(path), a, b))
                except ValueError:
                    continue
            found = next_shapes
        return found

    return shapes | expand(tree, ())


def outer_charts(ctx, term, rank, edges, reverse):
    for tree in chart_trees(ctx, term):
        shape = tree_ctx(tree)
        top = [(path, i) for path, i in tip_paths(tree) if len(path) == rank]
        reachable = {}

        def ends(x):
            if x not in reachable:
                vertices = {x} | {e[0] if reverse else e[1] for e in edges}
                reachable[x] = [y for y in vertices
                                if routes([(y, x) if reverse else (x, y)], edges, None) is not None]
            return reachable[x]

        for template, sigma in charts(ctx, term, shape):
            for values in product(*(ends(sigma[i]) for _, i in top)):
                middle = list(sigma)
                for (_, i), value in zip(top, values):
                    middle[i] = value
                segments = [(sigma[i], middle[i]) for _, i in top]
                if reverse:
                    segments = [(b, a) for a, b in segments]
                yield tree, template, sigma, tuple(middle), segments


def primitives(left, alpha, right, beta):
    lift_left = inverse_substitution(left, alpha)
    lift_right = inverse_substitution(right, beta)
    pairs = {(v(i), y) for i, actual in enumerate(alpha) for y in lift_right(actual)}
    pairs.update((x, v(i)) for i, actual in enumerate(beta) for x in lift_left(actual))
    return pairs


def widths(tree):
    level, result = [tree], []
    while level:
        result.append(len(level))
        level = [child for node in level for child in node]
    return result


def populations(total, parents):
    if parents == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for others in populations(total - first, parents - 1):
                yield (first, *others)


def bounded_trees(bounds, parents=1):
    """Forests reaching the last specified level, with a total width bound at each level."""
    if not bounds:
        yield ((),) * parents
        return
    for size in range(1, bounds[0] + 1):
        for children in bounded_trees(bounds[1:], size):
            for counts in populations(size, parents):
                forest, pos = [], 0
                for n in counts:
                    forest.append(children[pos:pos + n])
                    pos += n
                yield tuple(forest)


def parallel_templates(shape, mu, nu, left_type, right_type):
    if left_type == STAR:
        if shape == (STAR,):
            yield v(0)
        return
    lift = inverse_substitution(shape, mu)
    possible = [[x for x in lift(a) if subst_tm(x, nu) == b]
                for a, b in zip(left_type[2:], right_type[2:])]
    for source, target in product(*possible):
        h = mk_coh(shape, arr(infer(shape, source), source, target), variables(shape))
        try:
            infer(shape, h)
        except TypeError_:
            continue
        yield h


def middles(left_tree, alpha, left_type, right_tree, beta, right_type):
    left, right = tree_ctx(left_tree), tree_ctx(right_tree)
    pairs = primitives(left, alpha, right, beta)
    for shape, terms in ((left, [x for x, _ in pairs]), (right, [y for _, y in pairs])):
        covered = set().union(*(fv_tm(t) for t in terms))
        if not set(maximal_vars(shape)) <= covered:
            return
    lo, hi = widths(left_tree), widths(right_tree)
    domains, bounds = {}, []
    for d in range(max(len(lo), len(hi))):
        group = [(x, y) for x, y in pairs if tdim_tm(left, x) == d]
        if not group:
            return
        domains[d] = group
        a = lo[d] if d < len(lo) else 0
        b = hi[d] if d < len(hi) else 0
        cap = a + b
        if all(x[0] == 'v' for x, _ in group):
            cap = min(cap, a)
        if all(y[0] == 'v' for _, y in group):
            cap = min(cap, b)
        bounds.append(cap)
    for tree, in bounded_trees(bounds[1:]):
        shape = tree_ctx(tree)
        tips = tip_paths(tree)
        for values in product(*(domains[len(path)] for path, _ in tips)):
            try:
                mu, nu = [sub_from(shape, target, {i: p[j] for (_, i), p in zip(tips, values)})
                          for j, target in enumerate((left, right))]
            except TypeError_:
                continue
            for h in parallel_templates(shape, mu, nu, left_type, right_type):
                x, y = subst_tm(h, mu), subst_tm(h, nu)
                if infer(left, x) != left_type or infer(right, y) != right_type:
                    continue
                if (len(fv_tm(x) | fv_ty(left_type)) == len(left)
                        and len(fv_tm(y) | fv_ty(right_type)) == len(right)):
                    assert subst_tm(x, alpha) == subst_tm(y, beta)
                    yield x, y


def realize(chart, mid, walks, alphabet, ctx, reverse):
    tree, template, sigma, alpha, _ = chart
    paths = {}
    it = iter(walks)
    rank = tdim_tm(tree_ctx(tree), template)
    for path, i in tip_paths(tree):
        paths[path] = (i, next(it) if len(path) == rank else ())
    if reverse:
        return assemble(ctx, tree, mid, template, alpha, paths, alphabet)
    return assemble(ctx, tree, template, mid, sigma, paths, alphabet)


def two_heads(ctx, source, target, alphabet=(), counts=None):
    """Two flat heads in succession with unrestricted intermediate syntax; return both or None."""
    rank = tdim_tm(ctx, source)
    ty = infer(ctx, source)
    if infer(ctx, target) != ty or any(tdim_tm(ctx, x) != rank + 1 for x in alphabet):
        raise ValueError('Expected parallel faces and top-dimensional labels')
    edges = [infer(ctx, x)[2:] for x in alphabet]
    if counts is not None:
        counts = tuple(counts)
        if len(counts) != len(edges) or any(type(i) is not int or i < 0 for i in counts):
            raise ValueError('Expected a nonnegative count for every letter')
    right_charts = list(outer_charts(ctx, target, rank, edges, True))
    for left in outer_charts(ctx, source, rank, edges, False):
        for right in right_charts:
            segments = left[4] + right[4]
            walks = routes(segments, edges, counts)
            if walks is None:
                continue
            mid = next(middles(left[0], left[3], infer(tree_ctx(left[0]), left[1]),
                               right[0], right[3], infer(tree_ctx(right[0]), right[1])), None)
            if mid is None:
                continue
            cut = len(left[4])
            a = realize(left, mid[0], walks[:cut], alphabet, ctx, False)
            b = realize(right, mid[1], walks[cut:], alphabet, ctx, True)
            a_type, b_type = infer(ctx, a), infer(ctx, b)
            assert a_type == arr(ty, source, b_type[2]) and b_type == arr(ty, a_type[3], target)
            return a, b
    return None


def cascades(suspensions, checker):
    from ct_suspension import susp_ctx, susp_tm
    from semistrict_surface_grid_tracks import associator, temporal
    ty = arr(STAR, v(0), v(0))
    ctx = (STAR,) + (ty,) * 5
    a, b, c, d, e = [v(i) for i in range(1, 6)]
    bc = temporal(ctx, b, c)
    cd = temporal(ctx, c, d)
    source = temporal(ctx, a, d)
    early = temporal(ctx, bc, d)
    late = temporal(ctx, b, cd)
    target = temporal(ctx, b, e)
    named = [arr(ty, a, bc), arr(ty, early, e), arr(ty, cd, e)]
    ctx += tuple(named)
    g, h, k = [v(i) for i in range(6, 9)]
    assoc = associator(ctx, b, c, d)
    data = (source, target, early, late, e, g, h, k, assoc)
    for _ in range(suspensions):
        ctx = susp_ctx(ctx)
        data = tuple(susp_tm(x) for x in data)
    source, target, early, late, e, g, h, k, assoc = data
    assert flat_head(ctx, source, e, (g, h)) is None
    found = two_heads(ctx, source, e, (g, h), (1, 1))
    assert found is not None
    rank = tdim_tm(ctx, source)
    fit = comp2(ctx, rank, *found)
    if checker:
        check_weak(checker, ctx, fit, arr(infer(ctx, source), source, e))
    assert two_heads(ctx, source, target, (g, k)) is None
    first = flat_head(ctx, source, early, (g,), (1,))
    last = flat_head(ctx, late, target, (k,), (1,))
    assert infer(ctx, assoc)[2:] == (early, late)
    three = comp2(ctx, rank, comp2(ctx, rank, first, assoc), last)
    assert infer(ctx, three)[2:] == (source, target)
    if checker:
        check_weak(checker, ctx, three, arr(infer(ctx, source), source, target))


def small_words():
    from semistrict_surface_grid_tracks import temporal
    ty = arr(STAR, v(0), v(0))
    a, b = v(1), v(2)
    ctx = (STAR, ty, ty, arr(ty, a, b), arr(ty, b, a))
    labels = (v(3), v(4))
    words = {(x,): x for x in (a, b)}
    words.update({(x, y): temporal(ctx, x, y) for x, y in product((a, b), repeat=2)})
    checked = 0
    for (l, s), (r, t) in product(words.items(), repeat=2):
        f = sum(x == a and y == b for x, y in zip(l, r))
        bwd = sum(x == b and y == a for x, y in zip(l, r))
        for i, j in product(range(3), repeat=2):
            expect = len(l) == len(r) and i - f == j - bwd >= 0
            assert (two_heads(ctx, s, t, labels, (i, j)) is not None) == expect
            checked += 1
    return checked


def chart_checks():
    from semistrict_surface_grid_tracks import temporal
    from relative_coherence_hidden_seam import identity
    from catt import glue_tree, ucomp
    checked = 0
    for tree in ((), disc_tree(1), disc_tree(2), glue_tree(1, 0, 1),
                 glue_tree(2, 0, 1), glue_tree(1, 0, 2), glue_tree(2, 1, 2), glue_tree(3, 2, 3)):
        ctx = tree_ctx(tree)
        total = ucomp(ctx)
        # Deep padded expressions have enormous written tuples. Compare complete
        # chart lists at low ranks and include both left and right ragged tips.
        terms = [total]
        if tdim_tm(ctx, total) < 2:
            terms.append(identity(ctx, total))
        if tdim_tm(ctx, total) == 1:
            terms.append(temporal(ctx, identity(ctx, infer(ctx, total)[2]), total))
        for term in terms:
            candidates = chart_trees(ctx, term)
            for size in range(1, 5):
                for other in trees_with_leaves(tdim_tm(ctx, term), size):
                    if other not in candidates:
                        assert next(charts(ctx, term, tree_ctx(other)), None) is None
                    checked += 1
    return checked


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path)
    args = parser.parse_args()
    print(f'{chart_checks()} candidate trees compared with literal chart inversion', flush=True)
    print(f'{small_words()} two-head multiplicity tests agree with the word formula', flush=True)
    with TemporaryDirectory() as scratch:
        checker = RankCut(6, args.checker.resolve(), Path(scratch)) if args.checker else None
        for suspensions in (0, 1, 4):
            cascades(suspensions, checker)
            print(f'Degree {suspensions + 2}: strict minima two and three for the two cascades', flush=True)
        for rank, width in ((2, 2), (5, 4)):
            ctx, witnesses = seam(rank, width, None)
            hidden, z = infer(ctx, witnesses[0])[2:]
            g = v(len(ctx) - 1)
            assert two_heads(ctx, hidden, z, [g]) is None
            assert two_heads(ctx, z, hidden, [g]) is None
            print(f'Degree {rank + 1}, width {width}: neither direction admits two flat heads', flush=True)
