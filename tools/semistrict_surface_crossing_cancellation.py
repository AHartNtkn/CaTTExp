"""Test the sharp completion threshold for a missing inner subdivision."""
from argparse import ArgumentParser
from pathlib import Path

from catt import comp2, infer, maximal_vars, src, tgt, v
from relative_coherence_exchange_faces import composite, head
from semistrict_surface_directed_power_queries import chart, crossing, row_fit
from semistrict_surface_grid_factors import padded_steps, place, write_module
from semistrict_surface_inverse_completion import DerivationEmitter
from semistrict_surface_thin_subdivision import partition_route


def data(size, first, long_left):
    ctx = chart(size + 1, 2) if long_left else chart(2, size + 1)
    tips = list(map(v, maximal_vars(ctx)))
    nleft = size + 1 if long_left else 2
    left, right = tips[:nleft], tips[nleft:]
    many, short = (left, right) if long_left else (right, left)
    if first:
        block, one = many[:-1], many[-1]
        single, other = short
    else:
        one, block = many[0], many[1:]
        other, single = short
    def pair(z, w):
        return (z, w) if long_left else (w, z)
    def whisker(z, w):
        return comp2(ctx, 0, *pair(z, w))
    moves = []
    for i in (range(size) if long_left else reversed(range(size))):
        before = [whisker(z, src(ctx, single)) for z in block[:i]]
        after = [whisker(z, tgt(ctx, single)) for z in block[i + 1:]]
        move = composite(ctx, 1, [*before, crossing(ctx, *pair(block[i], single)), *after])
        if moves and tgt(ctx, moves[-1]) != src(ctx, move):
            move = comp2(ctx, 2, row_fit(ctx, tgt(ctx, moves[-1]), src(ctx, move)), move)
        moves.append(move)
    g = crossing(ctx, *pair(one, other))
    f_start, f_end = ([single, *block], [*block, single]) if long_left else ([*block, single], [single, *block])
    g_end = list(pair(one, other))
    g_start = g_end[::-1]
    start, end = (f_start + g_start, f_end + g_end) if first else (g_start + f_start, g_end + f_end)
    return ctx, left, right, (moves + [g] if first else [g] + moves), start, end


def swaps(ctx, left, right, first, last):
    word = first.copy()
    order = {z: i for i, z in enumerate(last)}
    path = []
    while word != last:
        i = next(i for i, (x, y) in enumerate(zip(word, word[1:])) if order[x] > order[y])
        b, a = word[i:i + 2]
        assert b in right and a in left
        start = composite(ctx, 1, padded_steps(ctx, left, right, word))
        step = place(ctx, left, right, word, i, 2, crossing(ctx, a, b))
        word[i:i + 2] = [a, b]
        end = composite(ctx, 1, padded_steps(ctx, left, right, word))
        path.append(composite(ctx, 2, [row_fit(ctx, start, src(ctx, step)), step,
                                       row_fit(ctx, tgt(ctx, step), end)]))
    return path


def check(size, first, long_left, emitter):
    ctx, left, right, labels, start, end = data(size, first, long_left)
    before = swaps(ctx, left, right, right + left, start)
    after = swaps(ctx, left, right, end, left + right)
    assert sorted((len(before), len(after))) == [1, size]
    large = partition_route(ctx, labels, size, (size,), first)
    small = partition_route(ctx, labels, size, tuple(range(1, size + 1)), first)
    enter = row_fit(ctx, composite(ctx, 1, padded_steps(ctx, left, right, start)), src(ctx, src(ctx, large)))
    leave = row_fit(ctx, tgt(ctx, tgt(ctx, large)), composite(ctx, 1, padded_steps(ctx, left, right, end)))
    for i in range(len(before) + 1):
        for j in range(len(after) + 1):
            pre = composite(ctx, 2, [*before[len(before) - i:], enter])
            post = composite(ctx, 2, [leave, *after[:j]])
            a, b = [composite(ctx, 2, [pre, t, post]) for t in (large, small)]
            assert infer(ctx, a) == infer(ctx, b)
            if not emitter or size != 2:
                continue
            name = f'case{int(first)}{int(long_left)}{i}{j}'
            full = i == len(before) and j == len(after)
            emitter.checks.append(f'{name} : cohCase {emitter.ctx(ctx)} {emitter.ty(infer(ctx, a))} '
                                  f'{emitter.tm(a)} {emitter.tm(b)} ≡ {str(full).lower()}\n{name} = refl\n')
            if full:
                for side, s, t in [('Forth', a, b), ('Back', b, a)]:
                    cell = head(ctx, s, t)
                    emitter.check_type(name + side, ctx, cell, infer(ctx, cell))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = DerivationEmitter() if args.agda_dir else None
    for size in range(2, 7):
        for first in [True, False]:
            for long_left in [True, False]:
                check(size, first, long_left, emitter)
    if emitter:
        write_module(emitter, args.agda_dir, 'CrossingCancellation', __doc__)
    print('Checked 200 partial completions in four orientations, including both single-crossing whiskers.')


if __name__ == '__main__':
    main()
