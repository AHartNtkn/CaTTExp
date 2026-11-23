"""Check a three-column return context and directed sorting on changing edge paths."""

from argparse import ArgumentParser
from collections import Counter
from functools import lru_cache
from pathlib import Path

from catt import arr, chain_tree, check_ctx, comp2, infer, src, tgt, tree_ctx, v
from emit_agda import Emitter
from semistrict_surface_scalar_cube import cube_terms, exchange


def check_cube_with_returns(emitter):
    ctx = tree_ctx(chain_tree(3))
    edges = [v(i) for i in (2, 4, 6)]
    events = []
    for edge in edges:
        events.append(v(len(ctx)))
        ctx += (arr(infer(ctx, edge), edge, edge),)
    a, b, c = events
    for name, left, right in [('ab', a, b), ('bc', b, c),
                              ('ac', comp2(ctx, 0, a, edges[1]), c)]:
        swap = exchange(ctx, left, right)
        old, new = src(ctx, swap), tgt(ctx, swap)
        reverse = arr(infer(ctx, old), new, old)
        return_cell = v(len(ctx))
        ctx += (reverse,)
        emitter.check_type(name, ctx, return_cell, reverse)
    check_ctx(ctx)
    p, q, boundary = cube_terms(ctx, a, b, c)
    emitter.check_type('cube-negative', ctx, p, boundary)
    emitter.check_type('cube-positive', ctx, q, boundary)
    # The raw 4-type itself must be accepted before studying its inhabitation.
    reverse = arr(boundary, q, p)
    g = emitter.ctx(ctx)
    emitter.checks.append(f'reverse-type : {g} ⊢ty {emitter.ty(reverse)}\n'
                          f'reverse-type = from-just (checkTy {g} (from-just (checkCtx {g}))'
                          f' {emitter.ty(reverse)})\n')


INTERVALS = ((0, 2), (1, 3), (2, 4), (3, 5), (1, 4))
START = tuple(range(6))


def apply_step(path, interval):
    left, right = interval
    if left not in path or right not in path:
        return None
    i, j = path.index(left), path.index(right)
    if path[i:j + 1] == tuple(range(left, right + 1)):
        return path[:i + 1] + path[j:]
    if j == i + 1:
        return path[:i] + tuple(range(left, right + 1)) + path[j + 1:]
    return None


@lru_cache(None)
def positions(word):
    path = START
    result = []
    for interval in word:
        result.append(path.index(interval[0]))
        path = apply_step(path, interval)
        assert path is not None
    return tuple(result), path


def check_sorting(counts):
    @lru_cache(None)
    def normalize(word):
        pivots = [i for i in range(len(word) - 1) if word[i + 1][1] <= word[i][0]]
        assert all(i + 1 not in pivots for i in pivots)
        pos, end = positions(word)

        def swap(w, i):
            return w[:i] + (w[i + 1], w[i]) + w[i + 2:]

        for i in pivots:
            for j in pivots:
                if i < j:
                    assert swap(swap(word, i), j) == swap(swap(word, j), i)
                    counts["disjoint exchange diamonds"] += 1
        normal = None
        for i in pivots:
            moved = swap(word, i)
            new_pos, new_end = positions(moved)
            assert new_pos < pos and new_end == end
            candidate = normalize(moved)
            if normal is not None:
                assert candidate == normal
            normal = candidate
            counts["directed exchanges"] += 1
        counts["typed temporal lists"] += 1
        return word if normal is None else normal

    level = {(): START}
    for _ in range(7):
        for word in level:
            normalize(word)
        level = {word + (interval,): new for word, path in level.items()
                 for interval in INTERVALS if (new := apply_step(path, interval)) is not None}


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    check_cube_with_returns(emitter)
    counts = Counter()
    check_sorting(counts)
    if args.agda:
        module = emitter.module(args.agda.stem, 'A cube with a return for every pair.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n',
                                            'open import CaTTExp.Gray.Pure\n'))
    for label, count in sorted(counts.items()):
        print(f'{count:,} {label}')
