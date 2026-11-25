"""Check chronological rectangle factors and paste fifth-degree comparisons at shared rows."""
from argparse import ArgumentParser
from functools import cache
from itertools import combinations
from pathlib import Path

from catt import comp2, fv_tm, infer, maximal_vars, src, sub_from, subst_tm, tdim_tm, tgt, v
from ct_suspension import ident, susp_tm
from relative_coherence_exchange_faces import composite, head
from semistrict_surface_directed_power_queries import apply, chart, loop, row_fit, square
from semistrict_surface_inverse_completion import DerivationEmitter


def check_partitions(m, n):
    left, right = tuple(range(m)), tuple(range(m, m + n))
    def orders():
        for places in combinations(range(m + n), m):
            x, y = iter(left), iter(right)
            yield tuple(next(x) if i in places else next(y) for i in range(m + n))

    @cache
    def partition(events):
        rectangles = []
        for start in range(len(events)):
            rows, cols = set(), set()
            for stop in range(start + 1, len(events) + 1):
                a, b = events[stop - 1]
                rows.add(a)
                cols.add(b)
                if (max(rows) - min(rows) + 1) * (max(cols) - min(cols) + 1) == stop - start:
                    rectangles.append((start, stop))
        family = set(rectangles)
        for a, b in rectangles:
            for c, d in rectangles:
                if a < c < b < d:
                    assert {(a, d), (a, c), (c, b), (b, d)} <= family
        maximal = [(a, b) for a, b in rectangles
                   if not any(c <= a and b <= d and (a, b) != (c, d) for c, d in rectangles)]
        assert [i for a, b in maximal for i in range(a, b)] == list(range(len(events)))
        return tuple(maximal)

    count = 0
    def visit(word, events):
        nonlocal count
        count += 1
        parts = partition(events)
        for a, b in parts:
            for i in range(a, b - 1):
                x, y = events[i:i + 2]
                if x[0] != y[0] and x[1] != y[1]:
                    changed = events[:i] + (y, x) + events[i + 2:]
                    assert partition(changed) == parts
        for i, (b, a) in enumerate(zip(word, word[1:])):
            if b in right and a in left:
                visit(word[:i] + (a, b) + word[i + 2:], events + ((a, b),))
    for word in orders():
        visit(word, ())
    return count


def padded_steps(ctx, left, right, word):
    l, r = src(ctx, left[0]), src(ctx, right[0])
    steps = []
    for tip in word:
        if tip in left:
            steps.append(comp2(ctx, 0, tip, r))
            assert l == src(ctx, tip)
            l = tgt(ctx, tip)
        else:
            steps.append(comp2(ctx, 0, l, tip))
            assert r == src(ctx, tip)
            r = tgt(ctx, tip)
    return steps


def place(ctx, left, right, word, offset, width, change):
    steps = padded_steps(ctx, left, right, word)
    return composite(ctx, 1, [*steps[:offset], change, *steps[offset + width:]])


def clamp(ctx, left, right, small, l_start, r_start):
    l, ll, r, rr = map(v, maximal_vars(small))
    labels = []
    for side, start, pair in [(left, l_start, (l, ll)), (right, r_start, (r, rr))]:
        for i in range(len(side)):
            if i < start:
                labels.append(ident(small, src(small, pair[0])))
            elif i < start + 2:
                labels.append(pair[i - start])
            else:
                labels.append(ident(small, tgt(small, pair[1])))
    return sub_from(ctx, small, dict(zip(maximal_vars(ctx), labels, strict=True)))


def proper_squares(ctx, t):
    outer, chi = square(2)
    native = susp_tm(chi)

    def has_swap(term):
        if term[0] == 'v':
            return False
        _, arity, ty, labels = term
        tips = maximal_vars(arity)
        if (arity, ty) == (outer, chi[2]):
            return all(any(tdim_tm(ctx, v(j)) == 2 for j in fv_tm(labels[i])) for i in tips)
        return any(has_swap(labels[i]) for i in tips if tdim_tm(ctx, labels[i]) == 3)

    _, arity, ty, labels = t
    tips = maximal_vars(arity)
    if (arity, ty) == (native[1], native[2]):
        return int(all(has_swap(labels[i]) for i in tips))
    return sum(proper_squares(ctx, labels[i]) for i in tips if tdim_tm(ctx, labels[i]) == 4)


def check_paste(emitter):
    local, h = loop()
    g = src(local, h)
    padded = comp2(local, 3, ident(local, g), h)
    compare = head(local, h, padded)
    ctx = chart(3, 4)
    tips = list(map(v, maximal_vars(ctx)))
    left, right = tips[:3], tips[3:]
    a, b, c = left
    p, q, r, s = right
    first = [p, q, a, r, s, b, c]
    middle = [p, q, a, b, c, r, s]
    blocks = []
    for word, off, names in [(first, 3, (b, c, r, s)), (middle, 0, (a, b, p, q))]:
        blocks.append([place(ctx, left, right, word, off, 4, apply(ctx, (local, item), names))
                       for item in (h, padded, compare)])
    h1, p1, c1 = blocks[0]
    h2, p2, c2 = blocks[1]
    seam = row_fit(ctx, tgt(ctx, tgt(ctx, h1)), src(ctx, src(ctx, h2)))
    h1, p1, c1 = [comp2(ctx, 2, x, seam) for x in (h1, p1, c1)]
    def serial(f, g):
        return comp2(ctx, 3, comp2(ctx, 2, f, src(ctx, g)), comp2(ctx, 2, tgt(ctx, f), g))
    start, end = serial(h1, h2), serial(p1, p2)
    change_left = comp2(ctx, 3, comp2(ctx, 2, c1, src(ctx, h2)), comp2(ctx, 2, tgt(ctx, h1), h2))
    change_right = comp2(ctx, 3, comp2(ctx, 2, p1, src(ctx, p2)), comp2(ctx, 2, tgt(ctx, p1), c2))
    result = comp2(ctx, 4, change_left, change_right)
    assert (src(ctx, result), tgt(ctx, result)) == (start, end)
    for i, (l_start, r_start) in enumerate([(1, 2), (0, 0)]):
        sigma = clamp(ctx, left, right, local, l_start, r_start)
        assert [proper_squares(local, subst_tm(t, sigma)) for t in (h1, h2)] == [int(i == 0), int(i == 1)]
        assert proper_squares(local, subst_tm(start, sigma)) == 1
        assert proper_squares(local, subst_tm(end, sigma)) == 1
    if emitter:
        emitter.check_type('localFullFit', local, compare, infer(local, compare))
        emitter.check_type('twoFullFits', ctx, result, infer(ctx, result))
        emitter.checks.append(f'noGlobalHead : cohCase {emitter.ctx(ctx)} {emitter.ty(infer(ctx, start))} '
                              f'{emitter.tm(start)} {emitter.tm(end)} ≡ false\nnoGlobalHead = refl\n')


def write_module(emitter, directory, name, doc):
    directory.mkdir(parents=True, exist_ok=True)
    module = emitter.module(name, doc).replace(
        'open import CaTTExp.Pure\n', 'open import CaTTExp.Gray.Pure\n'
        'open import CaTTExp.Pure using (∅)\n'
        'open import CaTTExp.PastingCheck ∅ using () renaming (checkPs to pastable)\n')
    (directory / (name + '.agda')).write_text(module)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    count = sum(check_partitions(m, n) for m, n in [(2, 3), (3, 3), (2, 4), (3, 4)])
    emitter = DerivationEmitter() if args.agda_dir else None
    check_paste(emitter)
    if emitter:
        write_module(emitter, args.agda_dir, 'GridFactors', __doc__)
    print(f'Checked maximal rectangular factors on {count} histories and the two clamped fifth-degree fits.')


if __name__ == '__main__':
    main()
