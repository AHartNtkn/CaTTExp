"""Compare synchronized raw boundaries by their paired ordinary positional values."""

import argparse
from functools import cache
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, check_ctx, comp2, disc_tree, fv_tm, fv_ty, glue_tree, infer, maximal_vars, mk_coh,
                  src, sub_from, subst_tm, tdim_tm, tgt, tree_ctx, tree_of, v)
from relative_coherence_hidden_seam import identity
from semistrict_surface_flat_heads import check_weak, inverse_substitution, tip_paths
from semistrict_surface_grid_tracks import temporal
from semistrict_surface_insertion_cut import variables
from semistrict_surface_rank_cut import RankCut


def labelled_join(k, left, right):
    # A leaf integer names its generator. A tuple is the ordered list of branches.
    if k == 0:
        if isinstance(left, int):
            assert not isinstance(right, int) or left == right
            return right
        if isinstance(right, int):
            return left
        return left + right
    if isinstance(left, int):
        assert left == right
        return left
    assert len(left) == len(right)
    return tuple(labelled_join(k - 1, a, b) for a, b in zip(left, right))


@cache
def strict_tree(ctx, t):
    if t[0] == 'v':
        value = t[1]
        for _ in range(tdim_tm(ctx, t)):
            value = (value,)
        return value
    _, arity, _, args = t
    tree = tree_of(arity)
    tips = dict(tip_paths(tree))

    def expand(node, path):
        if not node:
            return strict_tree(ctx, args[tips[path]])
        total = expand(node[0], (*path, 0))
        for j in range(1, len(node)):
            total = labelled_join(len(path), total, expand(node[j], (*path, j)))
        return total

    return expand(tree, ())


def unlabel(value):
    return () if isinstance(value, int) else tuple(unlabel(child) for child in value)


class JointBoundary:
    """A pair of synchronized, parallel boundaries on finite globular contexts."""

    def __init__(self, contexts, substitutions, sources, targets):
        contexts, substitutions = tuple(contexts), tuple(substitutions)
        sources, targets = tuple(sources), tuple(targets)
        if not contexts or len({len(contexts), len(substitutions), len(sources), len(targets)}) != 1:
            raise ValueError('Expected one substitution and both boundaries per leg')
        rank = tdim_tm(contexts[0], sources[0])
        for ctx, a, b in zip(contexts, sources, targets):
            if infer(ctx, a) != infer(ctx, b) or tdim_tm(ctx, a) != rank:
                raise ValueError('Expected parallel boundaries of one dimension')
            for i, ty in enumerate(ctx):
                if tdim_tm(ctx, v(i)) > rank or (ty != STAR and any(t[0] != 'v' for t in ty[2:])):
                    raise ValueError('Expected globular contexts of height at most the boundary rank')
        for terms in (sources, targets):
            if len({subst_tm(t, sigma) for t, sigma in zip(terms, substitutions)}) != 1:
                raise ValueError('Boundary writings do not specialize equally')

        generators, declarations = [], []

        @cache
        def pair(terms):
            if any(t[0] == 'v' for t in terms):
                types = [infer(ctx, t) for ctx, t in zip(contexts, terms)]
                if types[0] == STAR:
                    ty = STAR
                else:
                    s, t = (pair(tuple(a[i] for a in types)) for i in (2, 3))
                    ty = arr(infer(tuple(declarations), s), s, t)
                index = len(declarations)
                generators.append(terms)
                declarations.append(ty)
                return v(index)
            _, arity, ty, _ = terms[0]
            assert all(t[1:3] == (arity, ty) for t in terms)
            return mk_coh(arity, ty, tuple(pair(args) for args in zip(*(t[3] for t in terms))))

        self.a, self.b = pair(sources), pair(targets)
        self.ctx = tuple(declarations)
        check_ctx(self.ctx)
        assert infer(self.ctx, self.a) == infer(self.ctx, self.b)
        self.projections = tuple(zip(*generators))
        self.left, self.right = strict_tree(self.ctx, self.a), strict_tree(self.ctx, self.b)
        self.contexts = contexts
        self.substitutions = substitutions

    def witness(self):
        if self.left != self.right:
            return None
        tree = unlabel(self.left)
        shape = tree_ctx(tree)
        tips = {}
        for path, i in tip_paths(tree):
            at = self.left
            for j in path:
                at = at[j]
            tips[i] = v(at)
        sigma = sub_from(shape, self.ctx, tips)
        lift = inverse_substitution(shape, sigma)
        for a, b in product(lift(self.a), lift(self.b)):
            ty = infer(shape, a)
            if ty != infer(shape, b):
                continue
            if any(len(fv_tm(t) | fv_ty(ty)) != len(shape) for t in (a, b)):
                continue
            h = mk_coh(shape, arr(ty, a, b), sigma)
            assert infer(self.ctx, h)[2:] == (self.a, self.b)
            result = tuple(subst_tm(h, mu) for mu in self.projections)
            assert len({subst_tm(t, alpha) for t, alpha in zip(result, self.substitutions)}) == 1
            for ctx, mu, term in zip(self.contexts, self.projections, result):
                assert infer(ctx, term)[2:] == (subst_tm(self.a, mu), subst_tm(self.b, mu))
            return result
        raise AssertionError('The common labelled positional value must lift both written boundaries')


def readings(ctx, labels):
    if len(labels) == 1:
        return labels[0], labels[0]
    left, right = labels[0], labels[-1]
    for t in labels[1:]:
        left = temporal(ctx, left, t)
    for t in reversed(labels[:-1]):
        right = temporal(ctx, t, right)
    return left, right


def ordered_partitions(size):
    for width in range(1, size + 1):
        for assignment in product(range(width), repeat=size):
            if set(assignment) == set(range(width)):
                yield assignment


def schedules(rank, legs, checker):
    shape = tree_ctx(disc_tree(rank))
    top = v(maximal_vars(shape)[0])
    lower = tree_ctx(disc_tree(rank - 1))
    ground = identity(lower, v(maximal_vars(lower)[0]))
    sigma = sub_from(shape, lower, {top[1]: ground})
    left_id, right_id = identity(shape, src(shape, top)), identity(shape, tgt(shape, top))
    examples = []
    for times in ordered_partitions(legs):
        first, second = [], []
        for slot in times:
            a, b = readings(shape, [left_id] * slot + [top] + [right_id] * (legs - slot - 1))
            first.append(a)
            second.append(b)
        examples.append((first, second))
    # The same folded source occurs in every schedule, even before conversion.
    assert len({subst_tm(t, sigma) for first, _ in examples for t in first}) == 1
    contexts, substitutions = [shape] * legs, [sigma] * legs
    for i, (a, _) in enumerate(examples):
        for j, (same_reading, b) in enumerate(examples):
            problem = JointBoundary(contexts, substitutions, a, same_reading)
            assert (problem.left == problem.right) == (i == j)
            if i != j:
                assert problem.witness() is None
                continue
            moves = JointBoundary(contexts, substitutions, a, b).witness()
            back = JointBoundary(contexts, substitutions, b, a).witness()
            loop = [temporal(ctx, f, g) for ctx, f, g in zip(contexts, moves, back)]
            units = [identity(ctx, t) for ctx, t in zip(contexts, a)]
            two = JointBoundary(contexts, substitutions, loop, units).witness()
            for terms in (moves, two):
                folded = subst_tm(terms[0], sigma)
                check_weak(checker, lower, folded, infer(lower, folded))
    # An incompatible pair still has coherent comparisons after folding.
    a, b = examples[0][0], examples[-1][0]
    assert JointBoundary(contexts, substitutions, a, b).witness() is None
    folded = []
    for left, right in zip(a, b):
        track = mk_coh(shape, arr(infer(shape, left), left, right), variables(shape))
        folded.append(subst_tm(track, sigma))
    assert len(set(folded)) > 1
    for first, other in product(folded, repeat=2):
        assert infer(lower, first) == infer(lower, other)
        higher = mk_coh(lower, arr(infer(lower, first), first, other), variables(lower))
        check_weak(checker, lower, higher, infer(lower, higher))
        for flags in (('--su',), ('--sua',)):
            assert checker.published_equal(lower, higher, identity(lower, first), flags)
    for slot in range(legs):
        a, b = readings(shape, [left_id] * slot + [top] + [right_id] * (legs - slot - 1))
        for t in (a, b):
            for flags in (('--su',), ('--sua',)):
                assert checker.published_equal(shape, t, top, flags)
    return len(examples)


def spatial(checker, rank, cut, other_rank):
    ctx = tree_ctx(glue_tree(rank, cut, other_rank))
    g, h = [v(i) for i in maximal_vars(ctx)]
    simultaneous = comp2(ctx, cut, g, h)
    if rank == other_rank:
        other = temporal(ctx, comp2(ctx, cut, g, src(ctx, h)), comp2(ctx, cut, tgt(ctx, g), h))
        assert not checker.published_equal(ctx, simultaneous, other)
    else:
        other = temporal(ctx, simultaneous, identity(ctx, tgt(ctx, simultaneous)))
    sigma = variables(ctx)
    problem = JointBoundary([ctx]*2, [sigma]*2, [simultaneous]*2, [other]*2)
    cells = problem.witness()
    assert cells[0] == cells[1]
    check_weak(checker, ctx, cells[0], arr(infer(ctx, other), simultaneous, other))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checker', type=Path)
    opts = parser.parse_args()
    with TemporaryDirectory() as scratch:
        checker = RankCut(6, opts.checker.resolve(), Path(scratch))
        for rank, legs in ((1, 3), (4, 2), (4, 3)):
            count = schedules(rank, legs, checker)
            print(f'Rank {rank}, {legs} legs: {count} joint classes, {count**2} comparisons; '
                  'all diagonal tracks and their round-trip comparisons checked', flush=True)
        for rank, cut, other in ((5, 0, 5), (5, 3, 5), (5, 1, 3)):
            spatial(checker, rank, cut, other)
            print(f'Spatial {rank}- and {other}-disc at cut {cut}: common raw comparison checked', flush=True)
