"""Critical reductions and the two interchanges for the walking bi-invertible arrow."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache, reduce
from pathlib import Path

from catt import (arr, chain_tree, coh_between, comp2, disc_tree, glue_tree, infer,
                  maximal_vars, sub_from, subst_tm, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from relative_coherence_walking_equivalence import walking_piece


def word_checks(bound):
    rules = (('c', 'b'), ('ab', ''), ('ba', ''))
    def steps(word):
        for i in range(len(word)):
            for left, right in rules:
                if word.startswith(left, i):
                    yield i, left, word[:i] + right + word[i + len(left):]

    @cache
    def normals(word):
        nexts = list(steps(word))
        if not nexts:
            return {word}
        return set().union(*(normals(result) for _, _, result in nexts))

    peaks = Counter()
    checked = 0
    frontier = [(x, x, '') for x in range(2)]
    for length in range(bound + 1):
        following = []
        for start, last, word in frontier:
            assert normals(word) == {'' if start == last else 'a' if start == 0 else 'b'}
            moves = list(steps(word))
            for i, lhs, left in moves:
                for j, rhs, right in moves:
                    if i < j < i + len(lhs):
                        assert left == right
                        peaks[word[i:j + len(rhs)]] += 1
            checked += 1
            for char in ('a' if last == 0 else 'bc'):
                following.append((start, 1 - last, word + char))
        frontier = following
    assert set(peaks) == {'aba', 'bab'}
    print(f'{checked} paths through length {bound}; overlap counts {dict(sorted(peaks.items()))}.')


def typed(file):
    ctx, checks = walking_piece()
    cells = {name: t for name, t, _, _ in checks}
    b, a = v(3), v(2)
    p, q, pi, qi = map(v, (5, 6, 7, 8))
    def comp(parts):
        return reduce(lambda s, t: comp2(ctx, 1, s, t), parts)
    d = comp((comp2(ctx, 0, cells['bc'], a), q))
    di = comp((qi, comp2(ctx, 0, cells['cb'], a)))
    disk = tree_ctx(disc_tree(1))
    x = v(2)
    def unit(t, left, expand):
        long = (comp2(disk, 0, identity(disk, v(0)), x) if left
                else comp2(disk, 0, x, identity(disk, v(1))))
        s, u = (x, long) if expand else (long, x)
        return coh_between(ctx, disc_tree(1), [t], s, u)
    chart = tree_ctx(chain_tree(3))
    x, y, z = map(v, maximal_vars(chart))
    l = comp2(chart, 0, comp2(chart, 0, x, y), z)
    r = comp2(chart, 0, x, comp2(chart, 0, y, z))
    emitter = Emitter()
    def verify(name, t, s, u):
        ty = arr(infer(ctx, s), s, u)
        assert infer(ctx, t) == ty
        if file:
            emitter.check_type(name, ctx, t, ty)
    for name, first, middle, left, right, li, ri in (
            ('aba', a, b, p, d, pi, di), ('bab', b, a, d, p, di, pi)):
        labels = sub_from(chart, ctx, dict(zip(maximal_vars(chart), (first, middle, first))))
        start = subst_tm(l, labels)
        assoc, inv = (subst_tm(head(chart, s, u), labels) for s, u in ((l, r), (r, l)))
        verify(name + 'Left', comp((comp2(ctx, 0, left, first), unit(first, True, False))), start, first)
        verify(name + 'Right', comp((assoc, comp2(ctx, 0, first, right), unit(first, False, False))), start, first)
        verify(name + 'LeftBack', comp((unit(first, True, True), comp2(ctx, 0, li, first))), first, start)
        verify(name + 'RightBack', comp((unit(first, False, True), comp2(ctx, 0, first, ri), inv)), first, start)
    square = tree_ctx(glue_tree(2, 0, 2))
    x, y = map(v, maximal_vars(square))
    xs, xt = infer(square, x)[2:]
    ys, yt = infer(square, y)[2:]
    left = comp2(square, 1, comp2(square, 0, x, ys), comp2(square, 0, xt, y))
    right = comp2(square, 1, comp2(square, 0, xs, y), comp2(square, 0, x, yt))
    for name, first in (('slide', cells['bc']), ('double', p)):
        labels = sub_from(square, ctx, dict(zip(maximal_vars(square), (first, p))))
        for suffix, s, t in (('Forward', left, right), ('Back', right, left)):
            verify(name + suffix, subst_tm(head(square, s, t), labels), subst_tm(s, labels), subst_tm(t, labels))
    if file:
        file.write_text(emitter.module(file.stem, 'Oriented peaks and the interchanges in the triangle argument.'))
    print('Both peak paths and expansions, and both interchanges in both orientations, have their literal types.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    word_checks(16)
    typed(args.agda)
