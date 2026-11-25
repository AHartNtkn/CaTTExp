"""Find a single raw head with a prescribed full-insertion class at literal old faces."""
import argparse
from collections import Counter
from functools import cache, cached_property
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (TypeError_, arr, coh_between, comp2, disc_tree, glue_tree, infer, maximal_vars, mk_coh,
                  src, tdim_tm, tgt, tree_ctx, v)
from relative_coherence_hidden_seam import identity
from semistrict_surface_flat_heads import assemble, charts, check_weak, routes, tip_paths
from semistrict_surface_grid_tracks import temporal
from semistrict_surface_rank_cut import RankCut
from semistrict_surface_two_heads import chart_trees


@cache
def bound(ctx, term):
    if term[0] == 'v':
        return 1
    rank = tdim_tm(ctx, term)
    return max(1, sum(bound(ctx, term[3][i]) for i in maximal_vars(term[1])
                      if tdim_tm(term[1], v(i)) == rank))


class MarkedHeads:
    def __init__(self, checker, ctx, source, target, labels, mark, flags=('--sua',)):
        self.checker = checker
        self.flags = flags
        self.ctx, self.source, self.target = ctx, source, target
        self.ty = infer(ctx, source)
        if infer(ctx, target) != self.ty:
            raise ValueError('The requested faces must be literally parallel')
        self.rank = tdim_tm(ctx, source)
        self.mark = mark
        self.labels = tuple(labels)
        for x in labels:
            if tdim_tm(ctx, x) != self.rank+1:
                raise ValueError('Expected a top-dimensional term')
            infer(ctx, x)
        if tdim_tm(ctx, mark) != self.rank + 1:
            raise ValueError('The mark must have the same rank as the sought head')
        # The marked expression can itself require conversion for formation.
        RankCut(self.rank + 1, checker.binary, checker.directory, flags).infer(ctx, mark)
        if not self.checker.published_equal(ctx, mark, mark, self.flags):
            raise ValueError('Expected a formed marked expression')
        self.edges = [infer(ctx, x)[2:] for x in labels]
        self.neutral = [i for i, (a, _) in enumerate(self.edges)
                        if self.equal(labels[i], identity(ctx, a))]
        self.neutral_edges = [self.edges[i] for i in self.neutral]
        self.active = [i for i in range(len(labels)) if i not in self.neutral]
        self.budget = bound(ctx, mark)

    @cache
    def equal(self, a, b):
        return a == b or self.checker.published_equal(self.ctx, a, b, self.flags)

    @cache
    def connected(self, a, b):
        return routes([(a, b)], self.neutral_edges, None) is not None

    def words(self, start, end, budget):
        if self.connected(start, end):
            yield ()
        if budget:
            for i in self.active:
                a, b = self.edges[i]
                if self.connected(start, a):
                    for suffix in self.words(b, end, budget-1):
                        yield (i, *suffix)

    def skeletons(self, segments, budget):
        if not segments:
            yield ()
            return
        for w in self.words(*segments[0], budget):
            for other in self.skeletons(segments[1:], budget-len(w)):
                yield (w, *other)

    def choose_walks(self, segments, words, counts):
        absolute = Counter(i for word in words for i in word)
        if counts is not None and any(absolute[i] != counts[i] for i in self.active):
            return None
        gaps = []
        for (start, end), word in zip(segments, words):
            at = start
            for i in word:
                gaps.append((at, self.edges[i][0]))
                at = self.edges[i][1]
            gaps.append((at, end))
        budget = None if counts is None else tuple(counts[i] for i in self.neutral)
        fillings = routes(gaps, self.neutral_edges, budget)
        if fillings is None:
            return None
        it = iter(fillings)
        walks = []
        for word in words:
            result = [self.neutral[j] for j in next(it)]
            for i in word:
                result.append(i)
                result.extend(self.neutral[j] for j in next(it))
            walks.append(result)
        return walks

    def candidates(self):
        ctx, s, t = self.ctx, self.source, self.target
        for tree in chart_trees(ctx, s) & chart_trees(ctx, t):
            shape = tree_ctx(tree)
            tips = tip_paths(tree)
            lower = [i for i in range(len(shape)) if tdim_tm(shape, v(i)) < self.rank]
            right = list(charts(ctx, t, shape))
            for p, sigma in charts(ctx, s, shape):
                for q, tau in right:
                    if infer(shape, p) != infer(shape, q) or any(sigma[i] != tau[i] for i in lower):
                        continue
                    segments = [(sigma[i], tau[i]) for path, i in tips if len(path) == self.rank]
                    for words in self.skeletons(segments, self.budget):
                        yield tree, p, q, sigma, segments, words

    def realize(self, tree, p, q, sigma, walks):
        it = iter(walks)
        paths = {path: (i, next(it) if len(path) == self.rank else ()) for path, i in tip_paths(tree)}
        term = assemble(self.ctx, tree, p, q, sigma, paths, self.labels)
        assert infer(self.ctx, term) == arr(self.ty, self.source, self.target)
        return term

    @cached_property
    def profiles(self):
        """Retain the finite chart/word choices, with arbitrary neutral walks in their gaps."""
        result = []
        for candidate in self.candidates():
            tree, p, q, sigma, segments, words = candidate
            representative = self.choose_walks(segments, words, None)
            if self.equal(self.realize(tree, p, q, sigma, representative), self.mark):
                result.append(candidate)
        return result

    def find(self, counts=None):
        if counts is not None:
            counts = tuple(counts)
            if len(counts) != len(self.edges) or any(type(n) is not int or n < 0 for n in counts):
                raise ValueError('Expected a nonnegative integer count per label')
        for tree, p, q, sigma, segments, words in self.profiles:
            walks = self.choose_walks(segments, words, counts)
            if walks is not None:
                return self.realize(tree, p, q, sigma, walks)
        return None


def square(checker, n, cut):
    tree = glue_tree(n, cut, n)
    ctx = tree_ctx(tree)
    g, h = [v(i) for i in maximal_vars(ctx)]
    together = comp2(ctx, cut, g, h)
    first = temporal(ctx, comp2(ctx, cut, g, src(ctx, h)), comp2(ctx, cut, tgt(ctx, g), h))
    second = temporal(ctx, comp2(ctx, cut, src(ctx, g), h), comp2(ctx, cut, g, tgt(ctx, h)))
    ends = infer(ctx, together)[2:]
    for mark, yes in ((together, True), (first, False), (second, False)):
        solver = MarkedHeads(checker, ctx, *ends, (g, h), mark)
        w = solver.find()
        assert (w is not None) == yes
        if yes:
            check_weak(checker, ctx, w, arr(infer(ctx, ends[0]), *ends))
    assert not checker.published_equal(ctx, first, second)
    return ctx, tree, [g, h], together, first


def structural(checker, n):
    ctx, tree, tips, a, b = square(checker, n-1, 0)
    f = coh_between(ctx, tree, tips, a, b)
    back = coh_between(ctx, tree, tips, b, a)
    mark = temporal(ctx, f, back)
    solver = MarkedHeads(checker, ctx, a, a, (f, back), mark)
    assert solver.active == [0, 1] and solver.budget == 2
    for counts, yes in (((0, 0), False), ((1, 1), True), ((2, 2), False)):
        assert (solver.find(counts) is not None) == yes
    assert MarkedHeads(checker, ctx, a, a, (f, back), identity(ctx, a)).find((1, 1)) is None


def pruning(checker, n, flags):
    # Neutral moves between two different literal spellings precede a named move.
    disk = disc_tree(n-1)
    arity = tree_ctx(disk)
    x = v(len(arity)-1)
    p = temporal(arity, x, identity(arity, tgt(arity, x)))
    u = coh_between(arity, disk, [x], x, p)
    back = coh_between(arity, disk, [x], p, x)
    ty = infer(arity, x)
    y = v(len(arity))
    g = v(len(arity)+1)
    ctx = arity + (ty, arr(ty, p, y))
    formed = temporal(ctx, identity(ctx, p), g)
    labels = list(formed[3])
    labels[maximal_vars(formed[1])[0]] = identity(ctx, x)
    mark = mk_coh(formed[1], formed[2], labels)
    try:
        infer(ctx, mark)
    except TypeError_:
        pass
    else:
        raise AssertionError('Expected a mark whose tuple requires conversion')
    solver = MarkedHeads(checker, ctx, x, y, (u, back, g), mark, flags)
    assert solver.neutral == [0, 1]
    for i in range(4):
        for j in range(4):
            w = solver.find((i, j, 1))
            assert (w is not None) == (i == j + 1)
            if w is not None:
                assert checker.published_equal(ctx, w, mark, flags)
    assert solver.find((1, 0, 0)) is None


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checker', type=Path)
    opts = parser.parse_args()
    with TemporaryDirectory() as tmp:
        checker = RankCut(6, opts.checker.resolve(), Path(tmp))
        for n, cut in ((2, 0), (6, 0), (6, 4)):
            square(checker, n, cut)
            print(f'Degree {n}, cut {cut}: simultaneous class fits; both serial classes excluded', flush=True)
        for n in (3, 6):
            structural(checker, n)
            for flags in (('--su',), ('--sua',)):
                pruning(checker, n, flags)
            print(f'Degree {n}: zero-chain nonidentity cycle bounded; neutral walks retain exact counts', flush=True)
