"""Construct unrestricted raw fits at temporal words with compound structural interfaces."""

import argparse
from functools import cache, reduce
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (arr, chain_tree, coh_between, comp2, fv_tm, glue_tree, infer, maximal_vars,
                  mk_coh, sub_from, tree_ctx, ucomp, v)
from relative_coherence_hidden_seam import identity
from semistrict_surface_equal_rank import suspend
from semistrict_surface_exposed_paths import family
from semistrict_surface_flat_heads import assemble, charts, check_weak, inverse_substitution, routes, tip_paths
from semistrict_surface_grid_tracks import temporal
from semistrict_surface_rank_cut import RankCut
from semistrict_surface_two_heads import chart_trees


def fold(ctx, terms, cut):
    return reduce(lambda a, b: comp2(ctx, cut, a, b), terms)


def base_bridge(ctx, a, b):
    """Same strict cell at literal parallel faces on a globular base."""
    for tree in chart_trees(ctx, a) & chart_trees(ctx, b):
        shape = tree_ctx(tree)
        right = list(charts(ctx, b, shape))
        for p, sigma in charts(ctx, a, shape):
            for q, tau in right:
                if sigma == tau and infer(shape, p) == infer(shape, q):
                    ty = arr(infer(shape, p), p, q)
                    bridge = mk_coh(shape, ty, sigma)
                    assert infer(ctx, bridge) == arr(infer(ctx, a), a, b)
                    return bridge
    raise ValueError('Base cells have no common positional chart')


def guarded_head(solver, source, target, counts):
    decoded = tuple(solver.decode(x) for x in (source, target))
    words = [solver.colored_events(x) for x in decoded]
    if len(words[0]) != len(words[1]):
        return None
    walks = routes(list(zip(*words)), solver.edges, counts)
    if walks is None:
        return None
    rank, size = solver.rank, len(words[0])
    tree = suspend(chain_tree(size), rank - 1)
    shape = tree_ctx(tree)
    tips = tip_paths(tree)
    templates = []
    for word, term in zip(words, decoded):
        labels = [solver.new_z[i] for i in word] if size else [solver.atom]
        sigma = sub_from(shape, solver.collapsed, dict(zip(maximal_vars(shape), labels)))
        templates.append(next(iter(inverse_substitution(shape, sigma)(term))))
    labels = [solver.z[i] for i in words[0]] if size else [solver.attachment]
    sigma = sub_from(shape, solver.ctx, dict(zip(maximal_vars(shape), labels)))
    paths = {path: (i, walks[j] if size else ()) for j, (path, i) in enumerate(tips)}
    term = assemble(solver.ctx, tree, *templates, sigma, paths, solver.alphabet)
    assert infer(solver.ctx, term)[2:] == (source, target)
    return term


class TemporalBoundary:
    def __init__(self, solver, term):
        self.solver = solver
        self.ctx = solver.ctx
        self.rank = solver.rank
        self.term = term
        self.leaves = []
        self.base_only = []
        self.loop = infer(self.ctx, solver.z[0])
        if infer(self.ctx, term) != self.loop:
            raise ValueError('Expected a loop at the compound attachment')
        arity = tree_ctx(glue_tree(self.rank, self.rank - 1, self.rank))
        binary = ucomp(arity)
        tips = maximal_vars(arity)

        def parse(x):
            base = not fv_tm(x).intersection(z[1] for z in solver.z)
            if base or (infer(self.ctx, x) == self.loop and solver.decode(x) is not None):
                self.leaves.append(x)
                self.base_only.append(base)
                return len(self.leaves) - 1
            if x[0] == 'coh' and x[1:3] == binary[1:3]:
                return tuple(parse(x[3][i]) for i in tips)
            raise ValueError('Face is outside the temporal boundary class')

        self.pattern = parse(term)
        self.groups = []
        for i, base in enumerate(self.base_only):
            if i and base and self.base_only[i - 1]:
                self.groups[-1].append(i)
            else:
                self.groups.append([i])
        self.tree = suspend(chain_tree(len(self.leaves)), self.rank - 1)
        self.shape = tree_ctx(self.tree)
        self.pos = [v(i) for i in maximal_vars(self.shape)]
        self.grouped = [self.group(self.ctx, self.leaves, group) for group in self.groups]
        self.unit = identity(self.ctx, solver.attachment)
        self.corrected = [self.unit if self.base_only[g[0]] else x
                          for g, x in zip(self.groups, self.grouped)]
        self.guarded = fold(self.ctx, self.corrected, self.rank - 1)

    def group(self, ctx, labels, group):
        return fold(ctx, [labels[i] for i in group], self.rank - 1)

    def comparison(self, backward):
        def read(pattern):
            if isinstance(pattern, int):
                return self.pos[pattern]
            return temporal(self.shape, *(read(p) for p in pattern))

        source = read(self.pattern)
        groups = [self.group(self.shape, self.pos, g) for g in self.groups]
        target = fold(self.shape, groups, self.rank - 1)
        faces = (target, source) if backward else (source, target)
        rebracket = coh_between(self.ctx, self.tree, self.leaves, *faces)
        steps = []
        for group, original in zip(self.groups, self.grouped):
            if self.base_only[group[0]]:
                ends = (self.unit, original) if backward else (original, self.unit)
                steps.append(base_bridge(self.ctx, *ends))
            else:
                steps.append(identity(self.ctx, original))
        inside = fold(self.ctx, steps, self.rank - 1)
        witness = temporal(self.ctx, inside, rebracket) if backward else temporal(self.ctx, rebracket, inside)
        ends = (self.guarded, self.term) if backward else (self.term, self.guarded)
        assert infer(self.ctx, witness) == arr(self.loop, *ends)
        return witness


def fit(solver, source, target, counts=None):
    if counts is not None:
        counts = tuple(counts)
        if len(counts) != len(solver.edges) or any(type(n) is not int or n < 0 for n in counts):
            raise ValueError('Expected a nonnegative count per graph edge')
    left, right = (TemporalBoundary(solver, x) for x in (source, target))
    middle = guarded_head(solver, left.guarded, right.guarded, counts)
    if middle is None:
        return None
    result = fold(solver.ctx, [left.comparison(False), middle, right.comparison(True)], solver.rank)
    assert infer(solver.ctx, result) == arr(left.loop, source, target)
    return result


def examples(rank, checker):
    solver, base = family(rank, 3, False)
    ctx, z, p = solver.ctx, solver.z, solver.attachment
    tips = [v(i) for i in maximal_vars(base)]
    q = fold(base, tips, rank - 2)
    assert q != p
    tree = suspend(chain_tree(3), rank - 2)
    out = coh_between(base, tree, tips, p, q)
    back = coh_between(base, tree, tips, q, p)
    def typ(x, y):
        return arr(infer(ctx, x), x, y)
    # The p -> q -> p excursion straddles an actual binary bracket.
    a = temporal(ctx, temporal(ctx, z[0], out), temporal(ctx, back, z[1]))
    b = temporal(ctx, temporal(ctx, out, temporal(ctx, back, z[1])), z[2])
    assert solver.decode(a) is None and solver.decode(b) is None
    witness = fit(solver, a, b, (1, 1, 0, 0))
    assert witness is not None
    if checker:
        check_weak(checker, ctx, witness, typ(a, b))
    positive = 1
    for budget, expected in (((1, 2, 1, 0), True), ((1, 1, 0, 2), False),
                             ((1, 0, 0, 0), False)):
        value = fit(solver, a, b, budget)
        assert (value is not None) == expected
        positive += expected
    assert fit(solver, b, a) is None
    shadow = temporal(ctx, out, back)
    pure = fit(solver, shadow, identity(ctx, p), (0, 0, 0, 0))
    assert pure is not None and fit(solver, shadow, z[0]) is None
    if checker:
        check_weak(checker, ctx, pure, typ(shadow, identity(ctx, p)))
    # Permuting two isolated colors preserves their multiset.
    u, w = temporal(ctx, z[0], z[3]), temporal(ctx, z[3], z[0])
    assert fit(solver, u, w) is None
    return positive + 1


def word_checks():
    solver, _ = family(2, 2, False)
    words = [(), (0,), (1,), (2,), (3,), *product(range(3), repeat=2)]
    terms = {w: (fold(solver.ctx, [solver.z[i] for i in w], 1) if w
                 else identity(solver.ctx, solver.attachment)) for w in words}

    @cache
    def interleavings(word, remaining):
        if not any(remaining):
            return {word}
        possible = set()
        for j, ((a, b), count) in enumerate(zip(solver.edges, remaining)):
            if count:
                rest = remaining[:j] + (count - 1,) + remaining[j + 1:]
                for i, current in enumerate(word):
                    if current == a:
                        possible.update(interleavings(word[:i] + (b,) + word[i + 1:], rest))
        return possible

    count = 0
    for s, t in product(words, repeat=2):
        for budget in product(range(2), repeat=4):
            witnessed = guarded_head(solver, terms[s], terms[t], budget)
            assert (witnessed is not None) == (t in interleavings(s, budget))
            count += 1
    return count


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path)
    args = parser.parse_args()
    print(f'{word_checks()} exact graph budgets checked against serialized changes of individual positions')
    with TemporaryDirectory() as scratch:
        checker = RankCut(6, args.checker.resolve(), Path(scratch)) if args.checker else None
        for rank in (2, 3, 5):
            cases = examples(rank, checker)
            print(f'Degree {rank + 1}: {cases} positive word repairs; direction, counts, order and length distinguished')
