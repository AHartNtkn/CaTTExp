"""Pack a Gray binary word rectangle into one instance of the elementary square."""
from argparse import ArgumentParser
from functools import cache, reduce
from itertools import permutations, product
from pathlib import Path

from catt import (comp2, disc_tree, glue_tree, infer, maximal_vars, src, sub_from, subst_tm, tdim_tm,
                  tgt, tree_ctx, ucomp, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_scalar_cube import exchange


def product_at(ctx, cut, terms):
    return reduce(lambda a, b: comp2(ctx, cut, a, b), terms)


def arguments(term):
    return [term[3][i] for i in maximal_vars(term[1])]


def binary(term):
    if term[0] != 'coh':
        return False
    return len(maximal_vars(term[1])) == 2 and term[2] == ucomp(term[1])[2]


def events(ctx, word):
    """Distribute whiskers at their actual addresses, keeping stationary terms literal."""
    if word[0] == 'v':
        return [word]
    if not binary(word):
        assert word == identity(ctx, src(ctx, word))
        return []
    a, b = arguments(word)
    dims = (tdim_tm(ctx, a), tdim_tm(ctx, b))
    if dims == (2, 2):
        assert word[1] == tree_ctx(glue_tree(2, 1, 2))
        return events(ctx, a) + events(ctx, b)
    if dims == (2, 1):
        return [comp2(ctx, 0, x, b) for x in events(ctx, a)]
    assert dims == (1, 2)
    return [comp2(ctx, 0, a, x) for x in events(ctx, b)]


def pack(ctx, first, second):
    assert infer(ctx, first) == infer(ctx, second)
    by_source = {src(ctx, v(i)): v(i) for i in range(len(ctx)) if tdim_tm(ctx, v(i)) == 2}

    def lift(path):
        if binary(path):
            left, right = (lift(t) for t in arguments(path))
            if (tdim_tm(ctx, left), tdim_tm(ctx, right)) == (2, 2):
                return exchange(ctx, left, right)
            return comp2(ctx, 0, left, right)
        chain = []
        current = path
        while current in by_source:
            step = by_source[current]
            chain.append(step)
            current = tgt(ctx, step)
        return product_at(ctx, 1, chain) if chain else path

    square = lift(src(ctx, first))
    assert tdim_tm(ctx, square) == 3
    for actual, packed in zip((first, second), infer(ctx, square)[2:]):
        assert infer(ctx, actual) == infer(ctx, packed)
        assert events(ctx, actual) == events(ctx, packed)
    return square


def word_spellings(ctx, steps):
    """All unpadded binary spellings with these addressed steps and stationary siblings."""
    @cache
    def visit(block):
        if not binary(block[0]) and len(block) == 1:
            return (block[0],)
        found = set()
        for cut in range(1, len(block)):
            for a, b in product(visit(block[:cut]), visit(block[cut:])):
                found.add(comp2(ctx, 1, a, b))
        if all(binary(t) for t in block):
            pairs = [arguments(t) for t in block]
            for side in (0, 1):
                fixed = pairs[0][1-side]
                if tdim_tm(ctx, fixed) == 1 and all(p[1-side] == fixed for p in pairs):
                    for inner in visit(tuple(p[side] for p in pairs)):
                        a, b = (inner, fixed) if side == 0 else (fixed, inner)
                        found.add(comp2(ctx, 0, a, b))
        return tuple(found)
    return visit(tuple(steps))


def check_restrictions(ctx, m, n, packed, direct, arrangement, emitter):
    small = tree_ctx(glue_tree(2, 0, 2))
    a, b = map(v, maximal_vars(small))
    elementary = exchange(small, a, b)

    def labels(cell, keep, length):
        return [identity(small, src(small, cell)) if i < keep else
                identity(small, tgt(small, cell)) if i > keep else cell for i in range(length)]

    tips = maximal_vars(ctx)
    moving = [x for x in tips if tdim_tm(ctx, v(x)) == 2]
    left_pole = src(ctx, src(ctx, v(moving[0])))
    right_pole = src(ctx, src(ctx, v(moving[m])))
    vertices = (src(small, src(small, a)), src(small, src(small, b)), tgt(small, src(small, b)))
    stationary = {}
    for x in set(tips) - set(moving):
        pole = src(ctx, v(x))[1]
        region = (pole >= left_pole[1]) + (pole >= right_pole[1])
        stationary[x] = identity(small, vertices[region])
    def generating_event(term):
        if term[0] == 'v':
            return term
        a, b = arguments(term)
        return generating_event(a if tdim_tm(small, a) == 2 else b)

    for i, j in product(range(m), range(n)):
        entries = labels(a, i, m) + labels(b, j, n)
        sigma = sub_from(ctx, small, stationary | dict(zip(moving, entries, strict=True)))
        value = subst_tm(packed, sigma)
        for face, expected in zip(infer(small, value)[2:], infer(small, elementary)[2:]):
            if arrangement == 'bare':
                assert infer(small, face) == infer(small, expected)
                assert events(small, face) == events(small, expected)
            else:
                assert [generating_event(t) for t in events(small, face)] == [
                    generating_event(t) for t in events(small, expected)]
        if emitter:
            generic = head(ctx, *infer(ctx, packed)[2:])
            restrict = subst_tm(head(ctx, generic, packed), sigma)
            name = f'restrict{arrangement}{m}by{n}at{i}and{j}'
            emitter.check_typed(name, small, restrict)
            folded = subst_tm(direct, sigma)
            emitter.check_typed(name+'Direct', small, folded)
            emitter.checks.append(f'{name}Top : topS {emitter.tm(folded)} ≡ topS {emitter.tm(elementary)}\n'
                                  f'{name}Top = refl\n')


def check(m, n, arrangement, emitter=None):
    # A stationary column or an identity leaf can be outside the fork or in
    # one of its two input branches. The source bracketing fixes which case.
    outside = arrangement == 'outside'
    gap = arrangement == 'gap'
    tree = (((),) * m, ((),) * n)
    if outside:
        tree = ((), *tree)
    if gap:
        tree = (tree[0], (), tree[1])
    ctx = tree_ctx(tree)
    tips = [v(i) for i in maximal_vars(ctx)]
    marks = [t for t in tips if tdim_tm(ctx, t) == 2]
    a, b = product_at(ctx, 1, marks[:m]), product_at(ctx, 1, marks[m:])
    if gap:
        a = comp2(ctx, 0, a, tips[m])
    if arrangement == 'unit':
        unit = identity(ctx, src(ctx, src(ctx, b)))
        b = comp2(ctx, 0, unit, b)
    original = exchange(ctx, a, b)
    if outside:
        original = comp2(ctx, 0, tips[0], original)
    start, end = infer(ctx, original)[2:]

    def distributed(word):
        steps = events(ctx, word)
        result = identity(ctx, tgt(ctx, word))
        for step in reversed(steps):
            result = comp2(ctx, 1, step, result)
        return result

    left, right = distributed(start), distributed(end)
    packed = pack(ctx, left, right)
    assert packed == original
    generic = head(ctx, start, end)
    check_restrictions(ctx, m, n, packed, head(ctx, left, right), arrangement, emitter)
    spellings = 0
    if m == n == 2:
        for word in (start, end):
            steps = events(ctx, word)
            for spelling in word_spellings(ctx, steps):
                assert infer(ctx, spelling) == infer(ctx, word) and events(ctx, spelling) == steps
                spellings += 1
    if emitter:
        tag = f'{arrangement}{m}by{n}'
        emitter.check_typed(tag+'Words', ctx, head(ctx, left, right))
        emitter.check_typed(tag+'Forward', ctx, head(ctx, generic, packed))
        emitter.check_typed(tag+'Backward', ctx, head(ctx, packed, generic))
    return spellings


def check_outer_identity(emitter):
    ctx = tree_ctx(((), disc_tree(1), ()))
    x, a, y = map(v, maximal_vars(ctx))
    def pad(t):
        return comp2(ctx, 0, x, comp2(ctx, 0, t, y))
    before, after = pad(identity(ctx, a)), identity(ctx, pad(a))
    emitter.check_typed('carryIdentity', ctx, head(ctx, before, after))
    emitter.check_typed('returnIdentity', ctx, head(ctx, after, before))


def check_inversions():
    # Occurrences carry both the column and the index in that column.
    # Restrict two interleavings to an entire pair of chosen occurrences.
    count = 0
    for lengths in ((2, 2), (3, 2), (2, 1, 2), (1, 1, 1, 1)):
        names = [i for i, n in enumerate(lengths) for _ in range(n)]
        orders = set(permutations(names))
        histories = [tuple((c, order[:j].count(c)) for j, c in enumerate(order)) for order in orders]
        for first, second in product(histories, repeat=2):
            if first == second:
                continue
            pair = next((a, b) for j, a in enumerate(first) for b in first[j+1:]
                        if second.index(b) < second.index(a))
            assert pair[0][0] != pair[1][0]
            assert tuple(x for x in first if x in pair) == pair
            assert tuple(x for x in second if x in pair) == pair[::-1]
            count += 1
    print(f'{count} distinct ordered pairs of shuffles restrict to opposite elementary walks')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    check_inversions()
    emitter = Emitter()
    count = spellings = 0
    for m, n, arrangement in product(range(1, 5), range(1, 5), ('bare', 'outside', 'gap', 'unit')):
        spellings += check(m, n, arrangement, emitter if (m, n) == (2, 1) else None)
        count += 1
    print(f'{count} rectangles: both distributed words match the packed square at their literal path tree')
    print(f'{spellings} unpadded binary face spellings on the two-by-two tests; 400 one-event-per-side restrictions')
    if args.agda_dir:
        check_outer_identity(emitter)
        module = 'GrayRectanglePacking'
        code = emitter.module(module, __doc__).replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure')
        (args.agda_dir / (module+'.agda')).write_text(code)
