"""Enumerate the two polygon tensor boundaries and measure directed Gray moves."""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import product
from pathlib import Path

from catt import arr, comp2, glue_tree, infer, maximal_vars, src, tgt, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from semistrict_surface_scalar_cube import exchange


def moves(word, sides):
    for col, (source, target) in enumerate(sides):
        if source[0] in word:
            pos = word.index(source[0])
            if word[pos:pos + len(source)] == source:
                yield (col,), word[:pos] + target + word[pos + len(source):]
    for i, (b, a) in enumerate(zip(word, word[1:])):
        if b[0] == 1 and a[0] == 0:
            yield (a, b), word[:i] + (a, b) + word[i + 2:]


def trace(readout, start, sides, masses, ancestry):
    word = start
    mass = dict(zip(start, masses))
    age = dict(zip(start, ancestry))
    h = Fraction(0)
    input_data = []
    for op in readout:
        input_data.append((mass.copy(), age.copy()))
        if len(op) == 1:
            source, target = sides[op[0]]
            h += sum(mass[w] for w in word[:word.index(source[0])])
            for w in target:
                mass[w] = sum(mass[x] for x in source) / len(target)
                age[w] = (1 + sum(age[x] for x in source)) / len(target)
        word = dict(moves(word, sides))[op]
    assert sum(mass[x] for x in word) == sum(masses)
    return h, tuple(mass[x] for x in word), tuple(age[x] for x in word), input_data


def check_tensor(lengths, counts):
    def path(col, face, size):
        return tuple((col, face, i) for i in range(size))

    a, u, b, v = (path(i // 2, i % 2, n) for i, n in enumerate(lengths))
    sides = ((a, u), (b, v))
    start, finish = b + a, u + v
    P, Q = (0,), (1,)

    @lru_cache(None)
    def readouts(word):
        if word == finish:
            return [()]
        return [(op,) + tail for op, new in moves(word, sides) for tail in readouts(new)]

    paths = readouts(start)
    # Quotient the readings by strict interchange of disjoint diagram steps.
    classes = {r: r for r in paths}

    def root(r):
        while r != classes[r]:
            classes[r] = classes[classes[r]]
            r = classes[r]
        return r

    def wires(op):
        return set(op if len(op) == 2 else sum(sides[op[0]], ()))

    for r in paths:
        for i, (x, y) in enumerate(zip(r, r[1:])):
            if wires(x).isdisjoint(wires(y)):
                other = r[:i] + (y, x) + r[i + 2:]
                assert other in classes
                classes[root(r)] = root(other)

    # Evaluate complete readouts on nonuniform rational input data.
    masses = [Fraction(2 * i + 3, i + 1) for i in range(len(start))]
    ancestry = [Fraction(i + 2, 3) for i in range(len(start))]
    data = {r: trace(r, start, sides, masses, ancestry) for r in paths}
    bounds = defaultdict(set)
    for r in paths:
        assert data[r][:3] == data[root(r)][:3]
        counts['typed polygon and square readouts'] += 1

    # The two tensor orientations give different rewrite windows.
    # Each window contains one polygon and the swaps of its entire side.
    laws = {}
    for w in b + v:
        laws[w] = (tuple((x, w) for x in a) + (P,),
                   (P,) + tuple((x, w) for x in u))
    for w in a + u:
        laws[w] = ((Q,) + tuple((w, y) for y in reversed(v)),
                   tuple((w, y) for y in reversed(b)) + (Q,))
    for r in paths:
        height, output_mass, output_age, prefix_data = data[r]
        for wire, (lhs, rhs) in laws.items():
            for i in range(len(r) - len(lhs) + 1):
                if r[i:i + len(lhs)] != lhs:
                    continue
                other = r[:i] + rhs + r[i + len(lhs):]
                assert other in classes
                next_height, next_mass, next_age, _ = data[other]
                current_mass, current_age = prefix_data[i]
                assert (output_mass, output_age) == (next_mass, next_age)
                assert next_height - height == current_mass[wire] > 0
                bounds[root(r)].add((root(other), wire, current_age[wire]))
                counts['whiskered polygon-interval moves'] += 1

    def rectangle(left, right):
        return tuple((x, y) for x in left for y in reversed(right))

    bottom = root((Q,) + rectangle(a, v) + (P,))
    top = root((P,) + rectangle(u, b) + (Q,))
    costs = []
    for face in (0, 1):
        required = frozenset(w for w in laws if w[1] == face)

        @lru_cache(None)
        def walk(node, remaining):
            if not remaining:
                return {Fraction(0)} if node == top else set()
            return {cost + rest for end, wire, cost in bounds[node] if wire in remaining
                    for rest in walk(end, remaining - {wire})}

        scores = walk(bottom, required)
        assert len(scores) == 1
        costs.append(scores.pop())
    assert costs == [sum(ancestry), sum(ancestry) + 2]
    counts['two-polygon tensor atoms'] += 1


def raw_prism(polygon_left):
    ranks = (3, 2) if polygon_left else (2, 3)
    ctx = tree_ctx(glue_tree(ranks[0], 0, ranks[1]))
    x, y = map(v, maximal_vars(ctx))
    p, b = (x, y) if polygon_left else (y, x)
    u, w = src(ctx, p), tgt(ctx, p)

    def compose(k, left, right):
        return comp2(ctx, k, left, right)

    if polygon_left:
        before = compose(1, compose(0, p, src(ctx, b)), compose(0, tgt(ctx, u), b))
        after = compose(1, compose(0, src(ctx, u), b), compose(0, p, tgt(ctx, b)))
        negative = compose(2, exchange(ctx, u, b), before)
        positive = compose(2, after, exchange(ctx, w, b))
    else:
        before = compose(1, compose(0, src(ctx, b), p), compose(0, b, tgt(ctx, u)))
        after = compose(1, compose(0, b, src(ctx, u)), compose(0, tgt(ctx, b), p))
        negative = compose(2, before, exchange(ctx, b, w))
        positive = compose(2, exchange(ctx, b, u), after)
    assert infer(ctx, negative) == infer(ctx, positive)
    return ctx, head(ctx, negative, positive), arr(infer(ctx, negative), negative, positive)


def raw_prisms():
    emitter = Emitter()
    for polygon_left in (True, False):
        ctx, prism, expected = raw_prism(polygon_left)
        name = 'left' if polygon_left else 'right'
        emitter.check_type(name + '-prism', ctx, prism, expected)
    return emitter


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    totals = Counter()
    for lengths in product(range(1, 4), repeat=4):
        check_tensor(lengths, totals)
    emitter = raw_prisms()
    if args.agda:
        module = emitter.module(args.agda.stem, 'The two directed polygon-interval orientations.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n',
                                            'open import CaTTExp.Gray.Pure\n'))
    for label, value in sorted(totals.items()):
        print(f'{value:,} {label}')
