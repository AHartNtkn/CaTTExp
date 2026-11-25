"""Build the two raw power-split faces and verify the full two-column Gray projection."""
from argparse import ArgumentParser
from functools import cache
from pathlib import Path

from catt import (comp2, fv_tm, fv_ty, glue_tree, infer, maximal_vars, src, sub_from, subst_tm,
                  tdim_tm, tgt, tree_ctx, v)
from catt_unit_ordered_exchange import temporal_words
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, string_tree
from semistrict_surface_full_head_arities import total


@cache
def square(rank):
    ctx = tree_ctx(glue_tree(rank, rank - 2, rank))
    left, right = map(v, maximal_vars(ctx))
    early, late = temporal_words(ctx, left, right, rank - 2, rank - 1)
    return ctx, head(ctx, late, early)


def apply(ctx, generic, labels):
    arity, cell = generic
    sigma = sub_from(arity, ctx, dict(zip(maximal_vars(arity), labels, strict=True)))
    return subst_tm(cell, sigma)


def crossing(ctx, a, b):
    return apply(ctx, square(tdim_tm(ctx, a)), (a, b))


def chart(left, right):
    return tree_ctx((((),) * left, ((),) * right))


def row_fit(ctx, a, b):
    """Rebracket an ordered row. Its generic comparison uses just one temporal column."""
    binary = tree_ctx(glue_tree(2, 1, 2))
    l, r = maximal_vars(binary)

    def leaves(t):
        if t[0] == 'coh' and t[1] == binary:
            return leaves(t[3][l]) + leaves(t[3][r])
        return [t]

    items = leaves(a)
    assert items == leaves(b)
    row = tree_ctx(string_tree(1, [2] * len(items)))
    def shape(t, variables):
        if t[0] == 'coh' and t[1] == binary:
            return comp2(row, 1, shape(t[3][l], variables), shape(t[3][r], variables))
        return next(variables)

    tip_vars = list(map(v, maximal_vars(row)))
    cmp = head(row, shape(a, iter(tip_vars)), shape(b, iter(tip_vars)))
    return apply(ctx, (row, cmp), items)


def loop():
    ctx = chart(2, 2)
    a, aa, b, bb = map(v, maximal_vars(ctx))
    f, ff = src(ctx, a), tgt(ctx, aa)
    g, gg = src(ctx, b), tgt(ctx, bb)
    middle = crossing(ctx, crossing(ctx, a, b), crossing(ctx, aa, bb))
    first = composite(ctx, 1, [comp2(ctx, 0, f, b), crossing(ctx, a, bb),
                               comp2(ctx, 0, aa, gg)])
    last = composite(ctx, 1, [comp2(ctx, 0, a, g), crossing(ctx, aa, b),
                              comp2(ctx, 0, ff, bb)])
    incoming = row_fit(ctx, tgt(ctx, first), src(ctx, src(ctx, middle)))
    outgoing = row_fit(ctx, tgt(ctx, src(ctx, middle)), src(ctx, last))
    track = composite(ctx, 2, [first, incoming, middle, outgoing, last])
    back = head(ctx, tgt(ctx, track), src(ctx, track))
    h = comp2(ctx, 3, track, back)
    assert src(ctx, h) == tgt(ctx, h)
    return ctx, h


def adjacent(ctx, generic_loop):
    a, aa, b, bb, c, cc = map(v, maximal_vars(ctx))
    f, ff = src(ctx, a), tgt(ctx, aa)
    start = comp2(ctx, 1, comp2(ctx, 0, f, b), comp2(ctx, 0, f, bb))
    end = comp2(ctx, 1, comp2(ctx, 0, ff, c), comp2(ctx, 0, ff, cc))
    x = comp2(ctx, 1, start, apply(ctx, generic_loop, (a, aa, c, cc)))
    y = comp2(ctx, 1, apply(ctx, generic_loop, (a, aa, b, bb)), end)
    seam = row_fit(ctx, tgt(ctx, src(ctx, x)), src(ctx, src(ctx, y)))
    x = comp2(ctx, 2, x, seam)
    assert src(ctx, x) == tgt(ctx, x) and src(ctx, y) == tgt(ctx, y)
    assert tgt(ctx, src(ctx, x)) == src(ctx, src(ctx, y))
    return x, y


def separated_loops(generic_loop):
    """Place each of the eight advances on a distinct outer span."""
    ctx = tree_ctx((((),),) * 8)
    gates = list(map(v, maximal_vars(ctx)))
    def successive(first, second):
        return comp2(ctx, 0, first, src(ctx, second)), comp2(ctx, 0, tgt(ctx, first), second)

    labels = [placed for i in range(0, 8, 2) for placed in successive(*gates[i:i + 2])]
    a = apply(ctx, generic_loop, labels[:4])
    b = apply(ctx, generic_loop, labels[4:])
    u, v_path = src(ctx, a), src(ctx, b)
    u1, v0 = tgt(ctx, u), src(ctx, v_path)
    left_end, right_start = tgt(ctx, u1), src(ctx, v0)
    x = comp2(ctx, 1, comp2(ctx, 0, a, right_start), comp2(ctx, 0, left_end, v0))
    y = comp2(ctx, 1, comp2(ctx, 0, u1, right_start), comp2(ctx, 0, left_end, b))
    assert tgt(ctx, src(ctx, x)) == src(ctx, src(ctx, y))
    return ctx, x, y


def parallel_split(p, shift=2, split_left=True):
    """Separate the p loop copies on the generic strip before identifying their labels."""
    base = chart(p, 1) if split_left else chart(1, p)
    labels = list(map(v, maximal_vars(base)))
    block, single = (labels[:-1], labels[-1]) if split_left else (labels[1:], labels[0])
    multi = composite(base, 1, block)

    def at(a, b):
        return (a, b) if split_left else (b, a)

    direct = crossing(base, *at(multi, single))
    pieces = []
    order = range(p) if split_left else reversed(range(p))
    for i in order:
        before = [comp2(base, 0, *at(z, src(base, single))) for z in block[:i]]
        after = [comp2(base, 0, *at(z, tgt(base, single))) for z in block[i + 1:]]
        pieces.append(composite(base, 1, [*before, crossing(base, *at(block[i], single)), *after]))
    # After suspension the generic arity is a single outer column. At every
    # fitted endpoint its ordinary positional support contains all the variables.
    ctx = base
    for _ in range(shift):
        ctx = susp_ctx(ctx)
        direct = susp_tm(direct)
        pieces = [susp_tm(step) for step in pieces]
    cursor = src(ctx, direct)
    chain = []
    for step in pieces:
        chain += [head(ctx, cursor, src(ctx, step)), step]
        cursor = tgt(ctx, step)
    chain.append(head(ctx, cursor, tgt(ctx, direct)))
    pasted = composite(ctx, shift + 2, chain)
    assert infer(ctx, direct) == infer(ctx, pasted)
    return ctx, direct, pasted


def strip_routes(size):
    """Enumerate contextual exchanges on the actual ordered three-histories."""
    start = ('B', *range(size))
    finish = (*range(size), 'B')
    paths = [(start, ())]
    answers = set()
    while paths:
        state, cuts = paths.pop()
        if state == finish:
            answers.add(cuts)
            continue
        j = state.index('B')
        for end in range(j + 1, len(state)):
            target = (*state[:j], *state[j + 1:end + 1], 'B', *state[end + 1:])
            paths.append((target, cuts + (end,)))
    masks = {tuple(j for j in range(1, size) if mask & (1 << (j - 1))) + (size,)
             for mask in range(1 << (size - 1))}
    assert answers == masks
    # Compute closure under subdivision independently of the endpoint encoding.
    seen = {(size,)}
    frontier = list(seen)
    while frontier:
        cuts = frontier.pop()
        for i, (low, high) in enumerate(zip((0, *cuts), cuts)):
            for mid in range(low + 1, high):
                divided = cuts[:i] + (mid,) + cuts[i:]
                if divided not in seen:
                    seen.add(divided)
                    frontier.append(divided)
    assert seen == answers
    return len(answers)


def check_weights():
    primes = [2, 3, 5, 7, 11]
    tests = 0
    for mask in range(1 << len(primes)):
        selected = {p for i, p in enumerate(primes) if mask >> i & 1}

        def weight(m):
            out = 1
            for q in selected:
                while m % q == 0:
                    m //= q
                    out *= q
            return out

        for p in primes:
            for m in range(1, 33):
                assert (weight(p * m) == p * weight(m)) == (p in selected)
                tests += 1
    return tests


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    grid = (((), ()), ((), (), (), ()))
    ctx, rectangle = total(grid)
    small = loop()
    x, y = adjacent(ctx, small)
    emitter = Emitter()
    emitter.check_typed('markedLoop', *small)
    emitter.check_typed('rectangle', ctx, rectangle)
    ty = emitter.ty(infer(ctx, rectangle))
    term = emitter.tm(rectangle)
    emitter.checks.append(f'fullRectangle : cohCase {emitter.ctx(ctx)} {ty} {term} {term} ≡ true\n'
                          'fullRectangle = refl\n')
    for side in (True, False):
        strip, direct, pasted = parallel_split(2, shift=1, split_left=side)
        assert tdim_tm(strip, direct) == 4 and direct != pasted
    for p in (2, 3):
        strip, direct, pasted = parallel_split(p)
        left = apply(ctx, (strip, direct), [x] * p + [y])
        right = apply(ctx, (strip, pasted), [x] * p + [y])
        assert infer(ctx, left) == infer(ctx, right)
        assert tdim_tm(ctx, left) == 5 and left != right
        if p == 2:
            emitter.check_typed('directStrip', strip, direct)
            emitter.check_type('pastedStrip', strip, pasted, infer(strip, direct))
            if args.agda_dir:
                boundary = emitter.ty(infer(ctx, left))
                emitter.checks.append(f'fullSpecialization : cohCase {emitter.ctx(ctx)} {boundary} '
                                      f'{emitter.tm(left)} {emitter.tm(right)} ≡ true\n'
                                      'fullSpecialization = refl\n')
    wide, wx, wy = separated_loops(small)
    strip, direct, pasted = parallel_split(2)
    wide_faces = [apply(wide, (strip, route), [wx, wx, wy]) for route in (direct, pasted)]
    assert infer(wide, wide_faces[0]) == infer(wide, wide_faces[1])
    for face in wide_faces:
        assert set(range(len(wide))) == set(fv_tm(face)) | set(fv_ty(infer(wide, face)))
    if args.agda_dir:
        boundary = emitter.ty(infer(wide, wide_faces[0]))
        emitter.checks.append(f'eightSpans : cohCase {emitter.ctx(wide)} {boundary} '
                              f'{emitter.tm(wide_faces[0])} {emitter.tm(wide_faces[1])} ≡ false\n'
                              'eightSpans = refl\n')
    if args.agda_dir:
        module = 'DirectedPowerQueries'
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        source = emitter.module(module, __doc__)
        (args.agda_dir / (module + '.agda')).write_text(
            source.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))
    schedules = sum(strip_routes(size) for size in range(1, 10))
    print(f'Typed both degree-six boundaries; checked {schedules} strip routes and '
          f'{check_weights()} charge comparisons.')


if __name__ == '__main__':
    main()
