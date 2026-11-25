"""Decide marked temporal composites of flat heads through a finite graph of raw faces."""

import argparse
from collections import defaultdict, deque
from functools import cache
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import STAR, arr, coh_between, comp2, disc_tree, glue_tree, infer, maximal_vars, src, tgt, tree_ctx, v
from relative_coherence_hidden_seam import identity
from semistrict_surface_flat_heads import check_weak
from semistrict_surface_grid_tracks import temporal
from semistrict_surface_marked_heads import MarkedHeads
from semistrict_surface_rank_cut import RankCut


def readings(ctx, stages, flags):
    """Binary readings of the positive stages; insertion identifies all associations."""
    if len(stages) == 1:
        yield stages[0]
        return
    splits = (len(stages) - 1,) if flags == ('--sua',) else range(1, len(stages))
    for k in splits:
        for a, b in product(readings(ctx, stages[:k], flags), readings(ctx, stages[k:], flags)):
            yield temporal(ctx, a, b)


class MarkedRoutes:
    def __init__(self, checker, ctx, source, target, arcs, labels, mark, flags=('--sua',)):
        self.ctx, self.checker, self.mark = ctx, checker, mark
        self.source, self.target = source, target
        self.labels, self.flags = tuple(labels), tuple(flags)
        if self.flags not in (('--su',), ('--sua',)):
            raise ValueError('Select published strict units or full insertion')
        # Validate the mark and the literal outer faces even for an empty graph.
        outer = MarkedHeads(checker, ctx, source, target, self.labels, mark, self.flags)
        self.maximum = outer.budget
        self.profiles = []
        self.outgoing = defaultdict(list)
        for a, b in dict.fromkeys(arcs):
            if infer(ctx, a) != outer.ty or infer(ctx, b) != outer.ty:
                raise ValueError('Expected parallel literal faces throughout the graph')
            solver = MarkedHeads(checker, ctx, a, b, self.labels, mark, self.flags)
            for tree, p, q, sigma, segments, words in solver.candidates():
                walks = solver.choose_walks(segments, words, None)
                representative = solver.realize(tree, p, q, sigma, walks)
                positive = not solver.equal(representative, identity(ctx, a))
                letters = sum(map(len, words))
                assert positive or letters == 0
                cost = max(1, letters) if positive else 0
                index = len(self.profiles)
                self.profiles.append((solver, (tree, p, q, sigma), segments, words, representative, cost))
                self.outgoing[a].append((index, b, cost))

    def realize_path(self, history):
        if not history:
            yield identity(self.ctx, self.source)
            return
        blocks, prefix = [], None
        for tag, head in history:
            if self.profiles[tag][-1] > 0:
                blocks.append(head if prefix is None else temporal(self.ctx, prefix, head))
                prefix = None
            elif blocks:
                blocks[-1] = temporal(self.ctx, blocks[-1], head)
            else:
                prefix = head if prefix is None else temporal(self.ctx, prefix, head)
        yield from readings(self.ctx, blocks or [prefix], self.flags)

    def find(self, counts=None, stages=None):
        if counts is not None:
            counts = tuple(counts)
            if len(counts) != len(self.labels) or any(type(x) is not int or x < 0 for x in counts):
                raise ValueError('Expected one nonnegative integer per label')
        if stages is not None and (type(stages) is not int or stages < 0):
            raise ValueError('Expected a nonnegative stage count')

        @cache
        def realize(tag, vector):
            solver, data, segments, words, representative, _ = self.profiles[tag]
            if vector is None:
                return representative
            walks = solver.choose_walks(segments, words, vector)
            return None if walks is None else solver.realize(*data, walks)

        initial = (self.source, (), counts, stages)
        previous = {initial: None}
        queue = deque([initial])
        while queue:
            state = queue.popleft()
            face, active, remaining, steps = state
            if face == self.target and (remaining is None or not any(remaining)) and steps in (0, None):
                at, history = state, []
                while previous[at] is not None:
                    at, tag, head = previous[at]
                    history.append((tag, head))
                history.reverse()
                for t in self.realize_path(history):
                    if self.checker.published_equal(self.ctx, t, self.mark, self.flags):
                        assert infer(self.ctx, t)[2:] == (self.source, self.target)
                        return t, tuple(head for _, head in history)
            if steps == 0:
                continue
            spent = sum(self.profiles[i][-1] for i in active)
            for tag, end, cost in self.outgoing[face]:
                if spent + cost > self.maximum:
                    continue
                next_active = (*active, tag) if cost else active
                vectors = (None,) if remaining is None else product(*(range(n + 1) for n in remaining))
                for vector in vectors:
                    rest = None if remaining is None else tuple(n - k for n, k in zip(remaining, vector))
                    new = (end, next_active, rest, None if steps is None else steps - 1)
                    if new in previous:
                        continue
                    head = realize(tag, vector)
                    if head is not None:
                        previous[new] = state, tag, head
                        queue.append(new)
        return None


def verify(solver, counts, stages, expected):
    result = solver.find(counts, stages)
    assert (result is not None) == expected, (counts, stages, expected)
    if result:
        t, heads = result
        if stages is not None:
            assert len(heads) == stages
        check_weak(solver.checker, solver.ctx, t,
                   arr(infer(solver.ctx, solver.source), solver.source, solver.target))
        assert solver.checker.published_equal(solver.ctx, t, solver.mark, solver.flags)
    return result


def square(checker, degree, cut):
    ctx = tree_ctx(glue_tree(degree, cut, degree))
    g, h = [v(i) for i in maximal_vars(ctx)]
    simultaneous = comp2(ctx, cut, g, h)
    g1 = comp2(ctx, cut, g, src(ctx, h))
    h2 = comp2(ctx, cut, tgt(ctx, g), h)
    h1 = comp2(ctx, cut, src(ctx, g), h)
    g2 = comp2(ctx, cut, g, tgt(ctx, h))
    s, t = infer(ctx, simultaneous)[2:]
    m, n = tgt(ctx, g1), tgt(ctx, h1)
    serial = temporal(ctx, g1, h2)
    for middle, expected in ((m, True), (n, False)):
        arcs = [(s, s), (s, t), (t, t), (s, middle), (middle, middle), (middle, t)]
        solver = MarkedRoutes(checker, ctx, s, t, arcs, (g, h), serial)
        verify(solver, None, None, expected)
        verify(solver, (1, 1), 1, False)
        verify(solver, (1, 1), 2, expected)
        verify(solver, (1, 1), 4, expected)
        if not expected:
            other = MarkedRoutes(checker, ctx, s, t, arcs, (g, h), temporal(ctx, h1, g2))
            verify(other, (1, 1), 2, True)


def neutral_cycle(checker, degree, flags):
    disc = disc_tree(degree - 1)
    ctx = tree_ctx(disc)
    x = v(len(ctx) - 1)
    y = temporal(ctx, x, identity(ctx, tgt(ctx, x)))
    u = coh_between(ctx, disc, [x], x, y)
    w = coh_between(ctx, disc, [x], y, x)
    z = v(len(ctx))
    g = v(len(ctx) + 1)
    ctx += (infer(ctx, x), arr(infer(ctx, x), y, z))
    arcs = [(x, y), (y, x), (y, z)]
    solver = MarkedRoutes(checker, ctx, x, z, arcs, (u, w, g), g, flags)
    for steps in range(7):
        verify(solver, (3, 2, 1), steps, steps in (2, 4, 6))
    verify(solver, (2, 3, 1), None, True)
    for k, steps in product(range(4), range(11)):
        verify(solver, (0, k, 1), steps, steps >= 2*k + 2 and steps % 2 == 0)
    verify(solver, (3, 2, 0), None, False)


def associations(checker, flags):
    ctx = (STAR,) * 4 + tuple(arr(STAR, v(i), v(i + 1)) for i in range(3))
    letters = tuple(v(i) for i in range(4, 7))
    left, right = list(readings(ctx, letters, ('--su',)))
    assert checker.published_equal(ctx, left, right, flags) == (flags == ('--sua',))
    for mark in (left, right):
        solver = MarkedRoutes(checker, ctx, v(0), v(3), [(v(i), v(i+1)) for i in range(3)],
                              letters, mark, flags)
        verify(solver, (1, 1, 1), 3, True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checker', type=Path)
    opts = parser.parse_args()
    with TemporaryDirectory() as scratch:
        checker = RankCut(6, opts.checker.resolve(), Path(scratch))
        for flags in (('--su',), ('--sua',)):
            associations(checker, flags)
            neutral_cycle(checker, 6, flags)
            print(f'{flags[0]}: binary readings and neutral cycle budgets verified', flush=True)
        for degree, cut in ((2, 0), (6, 4)):
            square(checker, degree, cut)
            print(f'Degree {degree}, cut {cut}: only the prescribed serial seam fits its class', flush=True)
