"""Check marked interval refinements and the two-run reduction on labelled globe pairs."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from functools import cache
from itertools import product
from pathlib import Path

from canonical_gray_two_discs import tableau_interpreter
from catt import STAR, arr, check_ctx, comp2, infer, src, tgt, v
from emit_agda import Emitter
from gray_globe_attachments import ordered_factors
from gray_globe_comparison import atom, boundary, face, globe
from gray_globe_corner_prisms import fold
from gray_globe_corner_pullback import small_schroeder
from gray_globe_factorizations import rank, truncate
from gray_globe_section import cells
from gray_globe_strip_squares import chart_lift, minimal_shape


@cache
def native_order(w):
    """Fire actual enabled labelled events, breaking ties by first rank."""
    row = set(w[-2][0])
    pending = {rank(z)[0]: z for z in w[-1][0]}
    assert len(pending) == len(w[-1][0])
    word = []
    while pending:
        for i in sorted(pending):
            delta = boundary(pending[i])
            if set((-delta).elements()) <= row:
                break
        else:
            raise AssertionError("no enabled event")
        row.difference_update((-delta).elements())
        assert row.isdisjoint((+delta).elements())
        row.update((+delta).elements())
        word.append(i)
        del pending[i]
    assert row == set(w[-2][1])
    return tuple(word)


def grouped(w, first, last):
    d = len(w) - 1
    return ordered_factors(w, d - 1, {rank(z): first if first <= rank(z)[0] <= last
                                       else rank(z)[0] for z in w[-1][0]})


def interval_words(w, interval, stats):
    """Compare quotient-order expansion with the fine execution in the native tableau."""
    first, last = interval[0], interval[-1]
    pieces = grouped(w, first, last)
    words = [native_order(piece) for piece in pieces]
    coarse = sum(words, ())
    fine = native_order(w)
    block, = (word for word in words if first in word)
    if block == interval[::-1] or len(interval) == 1:
        assert coarse == fine
        return
    assert block == interval
    # Recover the exterior wings directly from the independently computed fine word.
    start, stop = fine.index(first), fine.index(last)
    left = tuple(i for i in fine[start:stop] if i < first)
    right = tuple(i for i in fine[start:stop] if i > last)
    assert left == tuple(range(first - 1, first - 1 - len(left), -1))
    assert right == tuple(range(last + len(right), last, -1))
    prefix, suffix = fine[:start], fine[stop+1:]
    assert fine == prefix + (first,) + left + interval[1:-1] + right + (last,) + suffix
    assert coarse == prefix + right + interval + left + suffix
    if left and right:
        stats['two wings'] += 1
        if len(interval) == 2:
            # Changing both ends of the displayed substring requires rotating the
            # entire substring if only one adjacent block transposition is used.
            initial = fine[start:stop+1]
            final = coarse[start:stop+1]
            assert all(initial[j:] + initial[:j] != final for j in range(1, len(initial)))
            stats['sharp binary'] += 1


def assembly(w, core, factors, emitter):
    """Check the implication from a chosen core term to the prescribed ungrouped caps."""
    cut = len(w) - 3
    ctx, values, names = (), [], {}

    def declare(cell):
        nonlocal ctx
        if cell not in names:
            if len(cell) == 1:
                ty = STAR
            else:
                a, b = (declare(face(cell, side)) for side in (0, 1))
                ty = arr(infer(ctx, a), a, b)
            names[cell] = v(len(ctx))
            values.append(cell)
            ctx += (ty,)
        return names[cell]

    def letters(cap):
        steps = ordered_factors(cap, cut, {rank(z): rank(z)[0] for z in cap[-1][0]})
        return [declare(step) for step in steps]

    core_words = [letters(face(core, s)) for s in (0, 1)]
    caps = [fold(ctx, cut, steps) for steps in core_words]
    ty = arr(infer(ctx, caps[0]), *caps)
    core_term = v(len(ctx))
    ctx += (ty,)
    values.append(core)
    pieces = [core_term if p == core else declare(p) for p in factors]
    lifted = fold(ctx, cut, pieces)
    words = [letters(face(w, s)) for s in (0, 1)]
    a, b = (fold(ctx, cut, steps) for steps in words)
    if a != src(ctx, lifted):
        pre = chart_lift(ctx, words[0], cut, a, src(ctx, lifted))
        lifted = comp2(ctx, cut+1, pre, lifted)
    if tgt(ctx, lifted) != b:
        post = chart_lift(ctx, words[1], cut, tgt(ctx, lifted), b)
        lifted = comp2(ctx, cut+1, lifted, post)
    check_ctx(ctx)
    expected = arr(infer(ctx, a), a, b)
    assert infer(ctx, lifted) == expected
    assert tableau_interpreter(ctx, values.__getitem__)(lifted) == w
    emitter.check_type('assembly-from-core', ctx, lifted, expected)


def check(m, n, emitter):
    domain = cells((m, n)) - {()}
    # Index the literal top rows of all proper iterated atom faces, including
    # those reached after lowering a formal marker more than one dimension.
    faces = defaultdict(set)
    for g in product(globe(m), globe(n)):
        rows = atom(g)
        for d, pair in enumerate(rows[1:-1], 1):
            for side, chain in enumerate(pair):
                w = truncate(rows, d, side)
                sites = tuple(sorted(rank(z)[0] for z in chain))
                assert sites == tuple(range(sites[0], sites[-1] + 1))
                assert native_order(w) == (sites[::-1] if side else sites)
                faces[d].add(frozenset(chain))
    stats = Counter()
    shapes = defaultdict(set)
    example = None
    for w in domain:
        d = len(w) - 1
        if not d:
            continue
        top = set(w[-1][0])
        for chain in faces[d]:
            if chain <= top:
                interval = tuple(sorted(rank(z)[0] for z in chain))
                interval_words(w, interval, stats)
                stats['marked rows'] += 1
                stats['longest interval'] = max(stats['longest interval'], len(interval))
        if d < 2 or len(top) != 1:
            continue
        g, = top
        i, j = rank(g)
        left, right = max(0, i-1), min(i, d-1)
        ends = [face(w, s) for s in (0, 1)]
        orders = list(map(native_order, ends))
        if left == right:
            first = last = orders[0].index(left)
            assert orders[0] == orders[1]
        else:
            # The decreasing face has a maximal consecutive decreasing run through the join.
            down = orders[1]
            first, last = down.index(right), down.index(left)
            assert last == first + 1
            while first and down[first-1] == down[first] + 1:
                first -= 1
            while last+1 < len(down) and down[last+1] == down[last] - 1:
                last += 1
            left_end, right_end = down[last], down[first]
            expected = tuple(range(left, left_end-1, -1)) + tuple(range(right_end, right-1, -1))
            assert orders[0] == down[:first] + expected + down[last+1:]
        core_sites = set(orders[1][first:last+1])
        owner = {rank(z): min(core_sites) if rank(z)[0] in core_sites else rank(z)[0]
                 for z in ends[0][-1][0]}
        owner[rank(g)] = min(core_sites)
        factors = ordered_factors(w, d-2, owner)
        core, = (p for p in factors if len(p) == d+1)
        assert all(p in domain for p in factors)
        if left != right and d-1 <= min(m, n):
            shapes[d-1, min(core_sites), max(core_sites), left].add(minimal_shape(core))
        for side, end in enumerate(ends):
            fine = ordered_factors(end, d-2, {rank(z): rank(z)[0] for z in end[-1][0]})
            expanded = []
            for p in factors:
                if p == core:
                    cap = face(p, side)
                    expanded.extend(ordered_factors(cap, d-2, {rank(z): rank(z)[0] for z in cap[-1][0]}))
                else:
                    expanded.append(p)
            assert tuple(expanded) == fine
        stats['singletons'] += 1
        stats['largest core'] = max(stats['largest core'], len(core_sites))
        if emitter and first > 0 and len(core_sites) >= 3 and left != right:
            candidate = w, core, factors
            if example is None or (len(w), w) < (len(example[0]), example[0]):
                example = candidate
    print(f"D^{m} x D^{n} (Gray): {dict(sorted(stats.items()))}")
    for degree in range(1, min(m, n) + 1):
        total = 0
        for lo in range(degree):
            for hi in range(lo+1, degree+1):
                expected = (small_schroeder(lo) if lo else 1)
                if hi < degree:
                    expected *= small_schroeder(degree-hi)
                for join in range(lo, hi):
                    assert len(shapes[degree, lo, hi, join]) == expected
                    total += expected
        print(f"Mixed degree-{degree+1} cores up to signed face inclusions: {total}")
    if emitter:
        if example is None:
            raise ValueError('the certificate needs a three-site core after a nonempty prefix')
        assembly(*example, emitter)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if min(args.m, args.n) < 1:
        parser.error('use positive globe dimensions')
    emitter = Emitter() if args.agda else None
    check(args.m, args.n, emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Assembling a prescribed two-run core.'))
