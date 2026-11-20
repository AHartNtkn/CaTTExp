"""Cellular coordinates in the based subcomputad with pure lower skeleton."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from pathlib import Path

from catt import (arr, check_ctx, coh_between, comp2, disc_tree, fv_tm, fv_ty,
                  infer, tdim, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_based_columns import Brackets
from relative_coherence_cut import top_counts
from relative_coherence_hidden_seam import identity


class BasedSkeleton:
    def __init__(self, ctx, point=0, through=3):
        self.ctx = ctx
        self.point = point
        self.through = through

    @cache
    def contains(self, term):
        ty = infer(self.ctx, term)
        if tdim(ty) + 1 <= self.through:
            return (fv_tm(term) | fv_ty(ty)) <= {self.point}
        return all(self.contains(pole) for pole in ty[2:])

    @cache
    def counts(self, term):
        if not self.contains(term):
            raise ValueError('term has an impure lower face')
        if term[0] == 'v' or any(not self.contains(t) for t in term[3]):
            return Counter({term: 1})
        counts = Counter()
        for slot, value in zip(term[1], term[3]):
            if tdim(slot) == tdim(term[2]):
                counts.update(self.counts(value))
        return counts

    def boundary(self, term):
        if not self.contains(term):
            raise ValueError('term has an impure lower face')
        source, target = infer(self.ctx, term)[2:]
        vector = self.counts(target).copy()
        vector.subtract(self.counts(source))
        return {key: value for key, value in vector.items() if value}


def hidden_unit(file):
    p = Brackets(1)
    point = v(0)
    lower = identity(p.ctx, identity(p.ctx, point))
    pure = identity(p.ctx, lower)
    hidden = p.bracket(lower, lower)
    left, right = p.bracket(pure, hidden), p.bracket(hidden, pure)
    ctx = p.ctx
    check_ctx(ctx)
    basis = BasedSkeleton(ctx)
    assert basis.contains(pure) and not basis.contains(hidden)
    first = comp2(ctx, 3, left, right)
    expanded = comp2(ctx, 3, left, identity(ctx, hidden))
    second = comp2(ctx, 3, expanded, right)
    assert top_counts(ctx, first) == top_counts(ctx, second) == Counter({left[1]: 1, right[1]: 1})
    assert first != second
    for term in (first, second):
        assert basis.counts(term) == {term: 1}
    disk = tree_ctx(disc_tree(4))
    x = v(len(disk) - 1)
    longer = comp2(disk, 3, x, identity(disk, infer(disk, x)[3]))
    emitter = Emitter()
    for name, s, t, a, b in (('insert', x, longer, first, second),
                              ('contract', longer, x, second, first)):
        local = coh_between(ctx, disc_tree(4), [left], s, t)
        witness = comp2(ctx, 3, local, right)
        expected = arr(infer(ctx, a), a, b)
        assert infer(ctx, witness) == expected
        assert basis.counts(witness) == {witness: 1}
        assert basis.boundary(witness) == {a: -1, b: 1}
        if file:
            emitter.check_type(name, ctx, witness, expected)
    if file:
        file.write_text(emitter.module(file.stem, 'Opposite five-columns in the based presentation.'))
    print('Two distinct reduced four-generators have the same ambient counts. '
          'Typed five-generators give both signed differences.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    hidden_unit(parser.parse_args().agda)
