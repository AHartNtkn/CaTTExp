"""Compile raw exchanges between disjoint placed events into counted trace rewriting."""
import argparse
from functools import cache
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (arr, check_ctx, coh_between, comp2, glue_tree, infer, maximal_vars, src,
                  subst_tm, tdim_tm, tgt, tree_ctx, v)
from relative_coherence_hidden_seam import identity
from semistrict_surface_compound_rewriting import Serial, search
from semistrict_surface_compound_words import fold
from semistrict_surface_flat_heads import check_weak
from semistrict_surface_grid_tracks import temporal
from semistrict_surface_rank_cut import RankCut


@cache
def events(ctx, t, rank):
    if tdim_tm(ctx, t) < rank:
        return ()
    if t[0] == 'v':
        return (t[1],)
    return tuple(e for j in maximal_vars(t[1]) if tdim_tm(t[1], v(j)) == rank
                 for e in events(ctx, t[3][j], rank))


class PlacedTraces:
    def __init__(self, base, ctx, rank, pole, weights, placements, exchanges, declarations):
        check_ctx(ctx)
        if ctx[:len(base)] != base or len(ctx) != len(base) + len(placements):
            raise ValueError('Supply one placement per ambient letter')
        self.rank = rank
        self.pole = pole
        self.aux = Serial(base, [(pole, pole)] * len(placements), rank, pole)
        if not weights:
            raise ValueError('Supply the weights of at least one lower generator')
        zero = (0,) * len(next(iter(weights.values())))
        if not zero or any(len(w) != len(zero) or any(type(n) is not int or n < 0 for n in w)
                           for w in weights.values()):
            raise ValueError('Expected nonnegative vectors of equal positive dimension')
        def weight(t):
            entries = [weights.get(i, zero) for i in events(base, t, rank - 1)]
            return tuple(sum(w[j] for w in entries) for j in range(len(zero)))
        cap = weight(pole)
        if not all(cap):
            raise ValueError('All capacity coordinates must be positive')
        supports = []
        for j, placed in enumerate(placements):
            index = len(base) + j
            ty = ctx[index]
            if tdim_tm(ctx, v(index)) != rank:
                raise ValueError('Expected a generating letter of the indicated rank')
            vec = weight(ty[2])
            if vec != weight(ty[3]) or not any(vec) or any(x not in (0, y) for x, y in zip(vec, cap)):
                raise ValueError('Letter faces must occupy the same nonempty set of whole coordinates')
            if infer(ctx, placed) != arr(infer(base, pole), pole, pole) or events(ctx, placed, rank) != (index,):
                raise ValueError('A placement must be a loop at the pole with exactly its own letter')
            supports.append({j for j, x in enumerate(vec) if x})
        self.ctx = ctx
        self.labels = tuple(v(i) for i in range(len(base))) + tuple(placements)
        self.rules = []
        for left, right in declarations:
            a, b = [w if w[:1] in (('v',), ('coh',)) else self.spell(w) for w in (left, right)]
            if any(infer(self.aux.ctx, face) != arr(infer(base, pole), pole, pole) for face in (a, b)):
                raise ValueError('Rule faces must be loops at the selected pole')
            s, t = subst_tm(a, self.labels), subst_tm(b, self.labels)
            self.aux.declare(a, b)
            self.rules.append((self.aux.word(a), self.aux.word(b)))
            self.labels += (v(len(self.ctx)),)
            self.ctx += (arr(infer(self.ctx, s), s, t),)
        check_ctx(self.ctx)
        self.swaps = []
        for i, j in product(range(len(placements)), repeat=2):
            if supports[i].isdisjoint(supports[j]):
                u, w = (i, j), (j, i)
                a, b = self.spell(u), self.spell(w)
                s, t = subst_tm(a, self.labels), subst_tm(b, self.labels)
                proof = exchanges[i, j]
                # Check in the rank-r skeleton, before any counted rules.
                if infer(ctx, proof) != arr(infer(ctx, s), s, t):
                    raise ValueError('Exchange has the wrong written boundary')
                self.swaps.append((u, w))
                self.aux.declare(a, b)
                self.labels += (proof,)

    def spell(self, word):
        if not word:
            return identity(self.aux.base, self.pole)
        return fold(self.aux.ctx, [self.aux.names[i] for i in word], self.rank - 1)

    def fit(self, source, target, counts=None, weights=None):
        pole_type = arr(infer(self.aux.base, self.pole), self.pole, self.pole)
        if any(infer(self.aux.ctx, x) != pole_type for x in (source, target)):
            raise ValueError('Query faces must be loops at the selected pole')
        a, b = self.aux.word(source), self.aux.word(target)
        history = search(self.rules, a, b, counts, weights, self.swaps)
        if history is None:
            return None
        lifted = self.aux.replay(source, target, history)
        witness = subst_tm(lifted, self.labels)
        s, t = subst_tm(source, self.labels), subst_tm(target, self.labels)
        assert infer(self.ctx, witness) == arr(infer(self.ctx, s), s, t)
        if counts is not None:
            seen = events(self.ctx, witness, self.rank + 1)
            first = len(self.ctx) - len(self.rules)
            assert tuple(seen.count(first + i) for i in range(len(self.rules))) == tuple(counts)
        return witness


def two_blocks(rank, cut, bubble=False, same_site=False):
    m = rank-1
    def double(node, depth):
        if depth == m-1:
            return node * 2
        return tuple(double(child, depth+1) for child in node)
    base = tree_ctx(double(glue_tree(m, cut, m), 0))
    a, b, c, d = [v(i) for i in maximal_vars(base)]
    p, q = temporal(base, a, b), temporal(base, c, d)
    whole = comp2(base, cut, p, q)
    ctx = base + tuple(arr(infer(base, t), t, t) for t in (p, p if same_site else q, whole))
    x, y, barrier = [v(len(base) + i) for i in range(3)]
    placed_y = comp2(ctx, cut, y, q) if same_site else comp2(ctx, cut, p, y)
    placements = (comp2(ctx, cut, x, q), placed_y, barrier)
    stencil = glue_tree(rank, cut, rank)
    square = tree_ctx(stencil)
    h, k = [v(i) for i in maximal_vars(square)]
    def mix(l, r):
        return comp2(square, cut, l, r)
    xy = temporal(square, mix(h, src(square, k)), mix(tgt(square, h), k))
    yx = temporal(square, mix(src(square, h), k), mix(h, tgt(square, k)))
    exchanges = {} if same_site else {(0, 1): coh_between(ctx, stencil, [x, y], xy, yx),
                                      (1, 0): coh_between(ctx, stencil, [x, y], yx, xy)}
    weights = {a[1]: (1, 0), b[1]: (1, 0), c[1]: (0, 1), d[1]: (0, 1)}
    if bubble:
        rules = [((), (1, 0)), ((0, 1), ())]
    else:
        # The rule's written source contains a lower-base structural excursion.
        aux = Serial(base, [(whole, whole)] * 3, rank)
        loop = coh_between(base, double(glue_tree(m, cut, m), 0), [a, b, c, d], whole, whole)
        decorated = temporal(aux.ctx, aux.names[0], temporal(aux.ctx, loop, aux.names[1]))
        rules = [(decorated, (2,))]
    return PlacedTraces(base, ctx, rank, whole, weights, placements, exchanges, rules)


def checks(rank, cut, checker):
    solver = two_blocks(rank, cut)
    for a, b in [((1, 0), (2,)), ((1, 0, 2), (2, 2))]:
        s, t = solver.spell(a), solver.spell(b)
        witness = solver.fit(s, t, (1,))
        assert witness is not None
        if checker:
            a, b = subst_tm(s, solver.labels), subst_tm(t, solver.labels)
            check_weak(checker, solver.ctx, witness, arr(infer(solver.ctx, a), a, b))
    assert solver.fit(solver.spell((0, 2, 1)), solver.spell((2, 2)), (1,)) is None
    assert solver.fit(solver.spell((0, 2)), solver.spell((2, 0)), (0,)) is None


def trace_checks():
    # The order on each occupied coordinate is invariant, and their lists
    # reconstruct the intervals between successive full-pole letters.
    words = [w for n in range(5) for w in product(range(3), repeat=n)]
    seen = 0
    for u, v0 in product(words, repeat=2):
        same = all([x for x in u if x != skip] == [x for x in v0 if x != skip] for skip in (0, 1))
        graph = search([], u, v0, (), free_rules=[((0, 1), (1, 0)), ((1, 0), (0, 1))])
        assert (graph is not None) == same
        seen += 1
    return seen


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path)
    opts = parser.parse_args()
    print(f'{trace_checks()} trace equalities agree with the two coordinate projections', flush=True)
    with TemporaryDirectory() as tmp:
        checker = RankCut(6, opts.checker.resolve(), Path(tmp)) if opts.checker else None
        for rank, cut in ((2, 0), (3, 0), (5, 0), (5, 3)):
            checks(rank, cut, checker)
            print(f'Degree {rank+1} at cut {cut}: certified exchanges, dependent order and rule blocking', flush=True)
        for same in (False, True):
            solver = two_blocks(3, 0, bubble=True, same_site=same)
            empty = solver.spell(())
            term = solver.fit(empty, empty, (1, 1))
            assert (term is None) == same
            if checker and term is not None:
                old = subst_tm(empty, solver.labels)
                check_weak(checker, solver.ctx, term, arr(infer(solver.ctx, old), old, old))
        print('Two opposite readings of the fourth-dimensional birth and death distinguished')
