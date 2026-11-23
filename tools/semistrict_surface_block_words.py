"""Check block-word factorization, positional lifts and returns across an object fold."""

from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import product
from math import factorial, prod
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, subst_tm, subst_ty, v
from emit_agda import Emitter
from relative_coherence_cut import outer_edge
from relative_coherence_hidden_seam import identity
from semistrict_surface_path_lift import columns
from semistrict_surface_scalar_cube import exchange


def runs(letters):
    intervals, positions = [], []
    for x, y in letters:
        if intervals and intervals[-1][1] == x:
            intervals[-1] = intervals[-1][0], y
        else:
            intervals.append((x, y))
        positions.append(len(intervals) - 1)
    return tuple(intervals), tuple(positions)


def shuffle_check(counts):
    ends = {'f': (0, 1), 'g': (1, 2), 'k': (0, 2), 'l': (1, 1)}
    rules = [('fg', 'k'), ('k', 'fg'), ('l', 'l'), ('f', 'f')]

    @cache
    def local_histories(word, depth):
        if depth == 0:
            return [(word, ())]
        histories = []
        for name, (old, new) in enumerate(rules):
            for p in range(len(word)):
                if word.startswith(old, p):
                    updated = word[:p] + new + word[p + len(old):]
                    for end, tail in local_histories(updated, depth - 1):
                        histories.append((end, ((p, name),) + tail))
        return histories

    for size in range(1, 5):
        for letters in product(ends, repeat=size):
            start = ''.join(letters)
            sector, initial_slots = runs(map(ends.get, start))
            pieces = [''.join(a for a, slot in zip(letters, initial_slots) if slot == j)
                      for j in range(len(sector))]
            level = [(start, ((),) * len(sector))]
            for depth in range(1, 4):
                following = []
                for word, factors in level:
                    actual, slots = runs(map(ends.get, word))
                    assert actual == sector
                    for name, (old, new) in enumerate(rules):
                        for p in range(len(word)):
                            if not word.startswith(old, p):
                                continue
                            j = slots[p]
                            assert slots[p + len(old) - 1] == j
                            step = (p - slots.index(j), name)
                            new_factors = factors[:j] + (factors[j] + (step,),) + factors[j + 1:]
                            following.append((word[:p] + new + word[p + len(old):], new_factors))
                level = following
                expected = Counter()
                for lengths in product(range(depth + 1), repeat=len(pieces)):
                    if sum(lengths) != depth:
                        continue
                    multiplicity = factorial(depth) // prod(factorial(n) for n in lengths)
                    choices = [local_histories(piece, n) for piece, n in zip(pieces, lengths)]
                    for factors in product(*choices):
                        ends_at, histories = zip(*factors)
                        expected[''.join(ends_at), histories] += multiplicity
                assert Counter(level) == expected
                counts['products of contextual rewrite histories'] += len(expected)
                counts['interleaved readings'] += sum(expected.values())


def setup():
    ctx = [STAR] * 3

    def var(ty):
        term = v(len(ctx))
        ctx.append(ty)
        return term

    f, g, k, loop, back = [var(arr(STAR, v(i), v(j))) for i, j in
                           ((0, 1), (1, 2), (0, 2), (1, 1), (2, 0))]
    fg = comp2(tuple(ctx), 0, f, g)
    a = var(arr(infer(tuple(ctx), k), fg, k))
    b = var(arr(infer(tuple(ctx), k), k, fg))
    c = var(arr(infer(tuple(ctx), f), f, f))
    d = var(arr(infer(tuple(ctx), loop), loop, loop))
    ab, cg = comp2(tuple(ctx), 1, a, b), comp2(tuple(ctx), 0, c, g)
    p = var(arr(infer(tuple(ctx), ab), ab, cg))
    check_ctx(tuple(ctx))
    return tuple(ctx), (f, g, k, loop, back, a, b, c, d, p)


def lift_check(counts):
    ctx, gen = setup()
    point = (STAR,)
    folded, fold = [STAR], [v(0)] * 3
    point_map = fold.copy()
    for ty in ctx[3:]:
        folded.append(subst_ty(ty, fold))
        fold.append(v(len(folded) - 1))
        point_map.append(('coh', point, subst_ty(ty, point_map), (v(0),)))
    folded, fold, point_map = tuple(folded), tuple(fold), tuple(point_map)
    f, g, k, loop, back, a, b, c, d, p = [subst_tm(t, fold) for t in gen]
    old = {fold[i]: i for i in range(3, len(ctx))}

    @cache
    def grade(t):
        if t == v(0):
            return ()
        if t[0] == 'v':
            return (outer_edge(ctx[old[t]]),)
        return runs(h for i in columns(t[1])[1] for h in grade(t[3][i]))[0]

    @cache
    def chain(w):
        vertices, total = [], 0
        for j, (s, _) in enumerate(w):
            block = []
            for x in range(3):
                if j and x == s:
                    block.append(vertices[-1][w[j - 1][1]])
                else:
                    block.append(v(total))
                    total += 1
            vertices.append(block)
        context = [STAR] * total
        forget, copies = [v(0)] * total, []
        for block in vertices:
            labels = block.copy()
            for i in range(3, len(ctx)):
                context.append(subst_ty(ctx[i], labels))
                labels.append(v(len(context) - 1))
                forget.append(fold[i])
            copies.append(tuple(labels))
        context = tuple(context)
        check_ctx(context)
        projections = []
        for focus, (s, t) in enumerate(w):
            proj = {}
            for j, labels in enumerate(copies):
                for i, var in enumerate(labels):
                    answer = v(i) if j == focus else subst_tm(point_map[i], (v(s if j < focus else t),))
                    assert var not in proj or proj[var] == answer
                    proj[var] = answer
            sigma = tuple(proj[v(i)] for i in range(len(context)))
            for i in range(len(context)):
                assert infer(ctx, sigma[i]) == subst_ty(context[i], sigma)
            projections.append(sigma)
        return context, tuple(forget), copies, projections

    def lift(t, before, after, w, copies):
        body = grade(t)
        full, slots = runs(before + body + after)
        assert full == w
        if t == v(0):
            if before:
                j = slots[len(before) - 1]
                return copies[j][before[-1][1]]
            return copies[0][w[0][0]]
        if t[0] == 'v':
            return copies[slots[len(before)]][old[t]]
        _, arity, ty, args = t
        sites, arrows = columns(arity)
        labels = [grade(args[i]) for i in arrows]
        actual = []
        for i, t1 in enumerate(args):
            j = sites[i]
            end = j if arity[i] == STAR else j + 1
            prefix = runs(before + sum(labels[:j], ()))[0]
            suffix = runs(sum(labels[end:], ()) + after)[0]
            actual.append(lift(t1, prefix, suffix, w, copies))
        return ('coh', arity, ty, tuple(actual))

    emitter = Emitter()
    mixed = exchange(folded, a, a)
    expressions = [mixed]
    for pre, mid, post in product((f, k, loop, back), (a, b, d, p), (f, g, k, loop)):
        expr = comp2(folded, 0, comp2(folded, 0, pre, mid), post)
        expressions.extend((expr, identity(folded, expr), comp2(folded, 0, expr, identity(folded, v(0)))))
    for expr in expressions:
        w = grade(expr)
        context, forget, copies, projections = chain(w)
        lifted = lift(expr, (), (), w, copies)
        assert subst_tm(lifted, forget) == expr
        ty = infer(context, lifted)
        assert subst_ty(ty, forget) == infer(folded, expr)
        assert tuple(lift(face, (), (), w, copies) for face in infer(folded, expr)[2:]) == ty[2:]
        for sigma in projections:
            assert infer(ctx, subst_tm(lifted, sigma)) == subst_ty(ty, sigma)
            counts['raw terms at projected block boundaries'] += 1
        if expr == mixed:
            assert len(w) == 2 and w[0] == w[1]
            emitter.check_type('lifted-two-copy-square', context, lifted, ty)
            for j, sigma in enumerate(projections):
                emitter.check_type(f'position-{j}', ctx, subst_tm(lifted, sigma), subst_ty(ty, sigma))
        counts['positional lifts at the folded boundary'] += 1
    return emitter


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    counts = Counter()
    shuffle_check(counts)
    emitter = lift_check(counts)
    if args.agda:
        module = emitter.module(args.agda.stem, 'An exchange across two distinct block occurrences.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n',
                                            'open import CaTTExp.Gray.Pure\n'))
    for label, total in sorted(counts.items()):
        print(f'{total:,} {label}')
