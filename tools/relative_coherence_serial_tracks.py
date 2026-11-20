"""Check top-row serializations, sorting forks, seam changes and substitution of a temporal composite."""

from argparse import ArgumentParser
from functools import reduce
from itertools import combinations, permutations
from pathlib import Path

from catt import (arr, chain_tree, check_ctx, comp2, disc_tree, glue_tree, infer, maximal_vars,
                  src, sub_from, subst_tm, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_chart_paths import unitor
from relative_coherence_exchange_faces import head


def swap(word, cut):
    return word[:cut] + (word[cut + 1], word[cut]) + word[cut + 2:]


def check_orders(n):
    pairs = tuple(combinations(range(n), 2))
    orders = tuple(permutations(range(n)))
    total_orders = squares = braids = 0
    for mask in range(1 << len(pairs)):
        edges = {edge for i, edge in enumerate(pairs) if mask >> i & 1}
        needs = [{('in', i)} | {(u, v) for u, v in edges if v == i} for i in range(n)]
        gives = [{('out', i)} | {(u, v) for u, v in edges if u == i} for i in range(n)]
        initial = {('in', j) for j in range(n)} | {'stationary'}
        terminal = {('out', j) for j in range(n)} | {'stationary'}
        legal = set()

        def visit(word, row):
            if len(word) == n:
                assert row == terminal
                legal.add(word)
                return
            for i in range(n):
                if i not in word and needs[i] <= row:
                    assert not (gives[i] & row)
                    visit(word + (i,), (row - needs[i]) | gives[i])

        visit((), initial)
        assert legal == {w for w in orders if all(w.index(u) < w.index(v) for u, v in edges)}
        total_orders += len(legal)
        for w in legal:
            moves = [j for j in range(n - 1) if w[j] > w[j + 1]]
            assert moves or w == tuple(range(n))
            assert all(swap(w, j) in legal for j in moves)
            for a, b in combinations(moves, 2):
                left, right = (a, b), (b, a)
                if b == a + 1:
                    left, right = (a, b, a), (b, a, b)
                    braids += 1
                else:
                    squares += 1
                def follow(path):
                    state = w
                    for j in path:
                        state = swap(state, j)
                        assert state in legal
                    return state
                assert follow(left) == follow(right)
        if n == 3 and not edges:
            assert len(legal) == sum(swap(w, j) in legal for w in legal for j in (0, 1)) // 2 == 6
    return len(range(1 << len(pairs))), total_orders, squares, braids


def path_arity(rank, width):
    path = chain_tree(width)
    for _ in range(rank - 1):
        path = (path,)
    return path


def check_seams(rank, emitter):
    chain = tree_ctx(path_arity(rank, 4))
    a, k, l, b = [v(i) for i in maximal_vars(chain)]

    def mul(u, w):
        return comp2(chain, rank - 1, u, w)

    def assoc(u, w, z):
        triple = tree_ctx(path_arity(rank, 3))
        x, y, t = (v(i) for i in maximal_vars(triple))
        def dot(i, j):
            return comp2(triple, rank - 1, i, j)
        alpha = head(triple, dot(dot(x, y), t), dot(x, dot(y, t)))
        return subst_tm(alpha, sub_from(triple, chain, dict(zip(maximal_vars(triple), (u, w, z)))))

    short_path = [assoc(mul(a, k), l, b), assoc(a, k, mul(l, b))]
    long_path = [mul(assoc(a, k, l), b), assoc(a, mul(k, l), b), mul(a, assoc(k, l, b))]
    def join(tracks):
        return reduce(lambda u, w: comp2(chain, rank, u, w), tracks)
    short, long = join(short_path), join(long_path)
    pentagon = head(chain, short, long)

    lower = tree_ctx(disc_tree(rank - 1))
    seam = v(len(lower) - 1)
    first = unitor(lower, seam)
    second = unitor(lower, tgt(lower, first))
    assert len({seam, tgt(lower, first), tgt(lower, second)}) == 3
    # The spatial source and target of each bridge are literally different.
    # The two external rank-m variables both survive strictification.
    ctx = lower + (infer(lower, seam), infer(lower, seam))
    start, end = v(len(lower)), v(len(lower) + 1)
    x = v(len(ctx))
    ctx += (arr(infer(ctx, seam), start, seam),)
    y = v(len(ctx))
    ctx += (arr(infer(ctx, seam), tgt(ctx, second), end),)
    check_ctx(ctx)
    sub = sub_from(chain, ctx, dict(zip(maximal_vars(chain), (x, first, second, y))))
    u, w, proof = (subst_tm(t, sub) for t in (short, long, pentagon))
    expected = arr(infer(ctx, u), u, w)
    assert u != w and infer(ctx, proof) == expected
    emitter.check_typed(f'seam-{rank}', ctx, proof)
    emitter.check_type(f'seam-{rank}', ctx, proof, expected)


def check_grafts(rank, emitter):
    lower_cut = rank - 2
    temporal_cut = rank - 1
    tree = (chain_tree(2), disc_tree(1))
    for _ in range(lower_cut):
        tree = (tree,)
    ctx = tree_ctx(tree)
    a, b, c = map(v, maximal_vars(ctx))
    pair = tree_ctx(glue_tree(rank, lower_cut, rank))
    x, y = map(v, maximal_vars(pair))

    def orders(left, right):
        forward = comp2(pair, temporal_cut, comp2(pair, lower_cut, left, src(pair, right)),
                        comp2(pair, lower_cut, tgt(pair, left), right))
        backward = comp2(pair, temporal_cut, comp2(pair, lower_cut, src(pair, left), right),
                         comp2(pair, lower_cut, left, tgt(pair, right)))
        return forward, backward

    forward, backward = orders(x, y)
    split = head(pair, comp2(pair, lower_cut, x, y), forward)
    exchange = head(pair, forward, backward)

    def specialize(track, left, right):
        return subst_tm(track, sub_from(pair, ctx, dict(zip(maximal_vars(pair), (left, right)))))

    ab = comp2(ctx, temporal_cut, a, b)
    nested = specialize(split, ab, c)
    first = comp2(ctx, lower_cut, a, src(ctx, c))
    last_swap = comp2(ctx, temporal_cut, first, specialize(exchange, b, c))
    expand = head(ctx, tgt(ctx, nested), src(ctx, last_swap))
    indirect = comp2(ctx, rank, comp2(ctx, rank, nested, expand), last_swap)
    direct = head(ctx, comp2(ctx, lower_cut, ab, c), tgt(ctx, last_swap))
    assert direct != indirect and infer(ctx, direct) == infer(ctx, indirect)
    proof = head(ctx, direct, indirect)
    emitter.check_typed(f'graft-{rank}', ctx, proof)
    emitter.check_type(f'graft-{rank}', ctx, proof, arr(infer(ctx, direct), direct, indirect))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    print('graphs, legal orders, square forks, braid forks:',
          tuple(map(sum, zip(*(check_orders(n) for n in range(1, 6))))))
    emitter = Emitter()
    for rank in (2, 3, 4):
        check_seams(rank, emitter)
        check_grafts(rank, emitter)
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Changes of seam and substitution of a temporal composite.'))
    print('Three seam-change pentagons and three nested substitutions verified')
