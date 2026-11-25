"""Find ordinary heads incident to one unspecified literal face."""

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


def primitives(shapes, substitutions, lifts, dimension):
    """Synchronized labels with a variable on at least one leg."""
    result = set()
    for leg, (shape, sigma) in enumerate(zip(shapes, substitutions)):
        for i, actual in enumerate(sigma):
            if tdim_tm(shape, v(i)) == dimension:
                choices = [(v(i),) if j == leg else lift(actual) for j, lift in enumerate(lifts)]
                result.update(product(*choices))
    return result


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


def common_preimages(shape, projections, terms):
    """All raw lifts of a fixed tuple through the given projections."""
    for x in inverse_substitution(shape, projections[0])(terms[0]):
        if all(subst_tm(x, mu) == t for mu, t in zip(projections[1:], terms[1:])):
            yield x


def parallel_templates(shape, projections, types):
    if types[0] == STAR:
        if shape == (STAR,):
            yield v(0)
        return
    possible = [common_preimages(shape, projections, terms) for terms in zip(*(ty[2:] for ty in types))]
    for source, target in product(*possible):
        h = mk_coh(shape, arr(infer(shape, source), source, target), variables(shape))
        try:
            infer(shape, h)
        except TypeError_:
            continue
        yield h


def shared_components(charts):
    """Yield (arity, projections, full representative) for the common middle writings."""
    trees, substitutions, types = zip(*charts)
    shapes = [tree_ctx(t) for t in trees]
    lifts = [inverse_substitution(shape, sigma) for shape, sigma in zip(shapes, substitutions)]
    levels = [widths(tree) for tree in trees]
    height = max(map(len, levels)) - 1
    domains, bounds = {}, [0] * (height + 1)
    for d in range(height, -1, -1):
        group = primitives(shapes, substitutions, lifts, d)
        if not group:
            return
        domains[d] = group
        sizes = [level[d] if d < len(level) else 0 for level in levels]
        bounds[d] = min([sum(sizes)] + [size for j, size in enumerate(sizes)
                                        if all(p[j][0] == 'v' for p in group)])
    for j, shape in enumerate(shapes):
        covered = set().union(*(fv_tm(p[j]) for group in domains.values() for p in group))
        if not set(maximal_vars(shape)) <= covered:
            return
    for tree, in bounded_trees(bounds[1:]):
        shape = tree_ctx(tree)
        tips = tip_paths(tree)
        for values in product(*(domains[len(path)] for path, _ in tips)):
            try:
                projections = tuple(sub_from(shape, target, {i: p[j] for (_, i), p in zip(tips, values)})
                                    for j, target in enumerate(shapes))
            except TypeError_:
                continue
            for h in parallel_templates(shape, projections, types):
                terms = [subst_tm(h, mu) for mu in projections]
                if all(infer(s, x) == ty and len(fv_tm(x) | fv_ty(ty)) == len(s)
                       for s, x, ty in zip(shapes, terms, types)):
                    assert len({subst_tm(x, sigma) for x, sigma in zip(terms, substitutions)}) == 1
                    yield shape, projections, h


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


def shared_heads(ctx, ports, alphabet=(), counts=None):
    """Find a raw head at each (fixed face, reverse) port, sharing one literal face."""
    ports = tuple(ports)
    if not ports:
        raise ValueError('Expected at least one port')
    alphabet = tuple(alphabet)
    rank = tdim_tm(ctx, ports[0][0])
    ty = infer(ctx, ports[0][0])
    if any(infer(ctx, t) != ty for t, _ in ports) or any(tdim_tm(ctx, x) != rank + 1 for x in alphabet):
        raise ValueError('Expected parallel faces and top-dimensional labels')
    edges = [infer(ctx, x)[2:] for x in alphabet]
    if counts is not None:
        counts = tuple(counts)
        if len(counts) != len(edges) or any(type(i) is not int or i < 0 for i in counts):
            raise ValueError('Expected a nonnegative count for every letter')
    choices = [outer_charts(ctx, term, rank, edges, reverse) for term, reverse in ports]
    for charts in product(*choices):
        segments = [segment for chart in charts for segment in chart[4]]
        walks = routes(segments, edges, counts)
        if walks is None:
            continue
        sections = [(tree, alpha, infer(tree_ctx(tree), template))
                    for tree, template, _, alpha, _ in charts]
        component = next(shared_components(sections), None)
        if component is None:
            continue
        _, projections, h = component
        start, heads = 0, []
        for chart, mu, (fixed, reverse) in zip(charts, projections, ports):
            stop = start + len(chart[4])
            mid = subst_tm(h, mu)
            head = realize(chart, mid, walks[start:stop], alphabet, ctx, reverse)
            actual = subst_tm(mid, chart[3])
            boundary = (actual, fixed) if reverse else (fixed, actual)
            assert infer(ctx, head) == arr(ty, *boundary)
            heads.append(head)
            start = stop
        return tuple(heads)
    return None


def two_heads(ctx, source, target, alphabet=(), counts=None):
    """Two successive flat heads with unrestricted intermediate syntax."""
    return shared_heads(ctx, ((source, False), (target, True)), alphabet, counts)


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
