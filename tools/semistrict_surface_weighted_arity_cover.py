"""Lift a computad and its terms into the bounded interval of a conserved arrow weight."""
from argparse import ArgumentParser
from functools import cache
from itertools import permutations, product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, subst_tm, subst_ty, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_return_edges import attachment, check_native_square


def poles(ty):
    while ty[1] != STAR:
        ty = ty[1]
    return ty[2][1], ty[3][1]


def plus(a, b):
    return tuple(x + y for x, y in zip(a, b, strict=True))


def minus(a, b):
    return tuple(x - y for x, y in zip(a, b, strict=True))


class Interval:
    def __init__(self, ctx, weights, width):
        self.ctx = ctx
        self.zero = (0,) * len(width)
        self.table, self.weights = {}, dict(weights)
        declarations, fold = [], []
        for i, ty in enumerate(ctx):
            if ty == STAR:
                weight = self.zero
            elif ty[1] == STAR:
                weight = self.weights[i]
                assert min(weight) >= 0
            else:
                weight = self.weight(ty[2])
                assert weight == self.weight(ty[3])
                self.weights[i] = weight
            for start in product(*(range(i + 1) for i in minus(width, weight))):
                lifted_type = STAR if ty == STAR else self.lift_type(ty, start, weight)
                self.table[i, start] = v(len(declarations))
                declarations.append(lifted_type)
                fold.append(v(i))
        self.window, self.fold = tuple(declarations), tuple(fold)
        check_ctx(self.window)
        for ty, generator in zip(self.window, self.fold, strict=True):
            assert subst_ty(ty, self.fold) == ctx[generator[1]]

    @cache
    def offsets(self, term):
        _, arity, ty, labels = term
        positions = {0: self.zero}
        for i, decl in enumerate(arity):
            if decl != STAR and decl[1] == STAR:
                s, t = poles(decl)
                pos = plus(positions[s], self.weight(labels[i]))
                assert positions.setdefault(t, pos) == pos
        origin = positions[poles(ty)[0]]
        return {i: minus(p, origin) for i, p in positions.items()}

    @cache
    def weight(self, term):
        if term[0] == 'v':
            return self.weights[term[1]]
        return self.offsets(term)[poles(term[2])[1]]

    @cache
    def lift(self, term, start):
        if term[0] == 'v':
            return self.table[term[1], start]
        _, arity, ty, labels = term
        positions = self.offsets(term)
        lifted = tuple(self.lift(label, plus(start, positions[i if decl == STAR else poles(decl)[0]]))
                       for i, (decl, label) in enumerate(zip(arity, labels, strict=True)))
        return 'coh', arity, ty, lifted

    def lift_type(self, ty, start, weight):
        if ty[1] == STAR:
            s, t = poles(ty)
            return arr(STAR, self.table[s, start], self.table[t, plus(start, weight)])
        return arr(self.lift_type(ty[1], start, weight),
                   self.lift(ty[2], start), self.lift(ty[3], start))

    def check_term(self, term, start):
        lifted = self.lift(term, start)
        assert infer(self.window, lifted) == self.lift_type(infer(self.ctx, term), start, self.weight(term))
        assert subst_tm(lifted, self.fold) == term
        return lifted


def check_windows(emitter):
    ctx = (STAR,)

    def declare(ty):
        nonlocal ctx
        gen = v(len(ctx))
        ctx += (ty,)
        return gen

    vertex = v(0)
    arrow = arr(STAR, vertex, vertex)
    a, b, c, d, z = [declare(arrow) for _ in range(5)]
    zero = identity(ctx, vertex)
    birth = declare(arr(arrow, zero, z))
    death = declare(arr(arrow, z, zero))
    pair = comp2(ctx, 0, a, b)
    gate = declare(arr(arrow, pair, c))
    branch = declare(arr(arrow, pair, c))
    step = declare(arr(infer(ctx, gate), gate, branch))
    loop = comp2(ctx, 1, birth, death)
    scalar = declare(arr(infer(ctx, loop), loop, identity(ctx, zero)))
    move = comp2(ctx, 0, a, scalar)
    top = declare(arr(infer(ctx, move), move, move))
    weights = {a[1]: 1, b[1]: 2, c[1]: 3, d[1]: 8, z[1]: 0}
    terms = [a, b, c, d, z, birth, death, gate, branch, step, loop, scalar, move, top, identity(ctx, step)]
    scalar_weights = {i: (w,) for i, w in weights.items()}
    rays = {a[1]: (1, 0, 0), b[1]: (0, 1, 0), c[1]: (1, 1, 0),
            d[1]: (0, 0, 1), z[1]: (0, 0, 0)}
    checked = 0
    for grading, bounds in ((scalar_weights, [(w,) for w in range(6)]),
                            (rays, list(product(range(3), range(3), (0,))))):
        for width in bounds:
            chart = Interval(ctx, grading, width)
            assert (d[1], chart.zero) not in chart.table
            assert sum(i == z[1] for i, _ in chart.table) == sum(i == 0 for i, _ in chart.table)
            for term in terms:
                w = chart.weight(term)
                for start in product(*(range(i + 1) for i in minus(width, w))):
                    new = chart.check_term(term, start)
                    checked += 1
                    if start == (0, 1, 0) and width == (2, 2, 0) and term in (gate, step, move, top):
                        name = f'placed{terms.index(term)}'
                        emitter.check_type(name, chart.window, new, chart.lift_type(infer(ctx, term), start, w))
    return checked


def check_returns():
    # A permutation on each of the parallel forward arrows and the return
    # need not preserve an individual sheet. Check directed reachability
    # on the whole lifted object graph in all such three-edge covers.
    count = 0
    for n in range(1, 5):
        sheets = range(n)
        for a, b, back in product(permutations(sheets), repeat=3):
            forward = {(i, n + p[i]) for i in sheets for p in (a, b)}
            edges = forward | {(n+i, back[i]) for i in sheets}
            for x, y in edges:
                reached, pending = {y}, [y]
                while pending:
                    z = pending.pop()
                    for s,t in edges:
                        if s == z and t not in reached:
                            reached.add(t)
                            pending.append(t)
                assert x in reached
            count += 1
    return count


def check_cyclic_attachment(emitter):
    ctx, words = attachment()
    returned = ctx + (arr(STAR, v(1), v(0)),)
    weights = {i: (0,) for i, ty in enumerate(ctx) if ty != STAR and ty[1] == STAR}
    weights[len(ctx)] = (1,)
    chart = Interval(returned, weights, (0,))
    assert chart.window == ctx
    assert tuple(chart.lift(t, (0,)) for t in words) == words
    for n in (1, 2, 3, 5):
        cyclic, projection, copies = [], [], []
        for _ in range(n):
            labels = []
            for i, ty in enumerate(ctx):
                cyclic.append(subst_ty(ty, labels))
                labels.append(v(len(cyclic) - 1))
                projection.append(v(i))
            copies.append(tuple(labels))
        for i, labels in enumerate(copies):
            cyclic.append(arr(STAR, labels[1], copies[(i + 1) % n][0]))
            projection.append(v(len(ctx)))
        cyclic = tuple(cyclic)
        check_ctx(cyclic)
        for i, label in enumerate(projection):
            assert subst_ty(cyclic[i], projection) == returned[label[1]]
        for labels in copies:
            left, right = (subst_tm(t, labels) for t in words)
            assert infer(cyclic, left) == infer(cyclic, right)
            assert (subst_tm(left, projection), subst_tm(right, projection)) == words
        if n == 2:
            emitter.check_typed('cyclicLeft', cyclic, left)
            emitter.check_typed('cyclicRight', cyclic, right)
    check_native_square()


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    placements = check_windows(emitter)
    check_cyclic_attachment(emitter)
    covers = check_returns()
    print(f'{placements} raw placements refold literally; all {covers} finite test covers have returns.')
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = 'WeightedArityCover'
        source = emitter.module(module, __doc__)
        (args.agda_dir / f'{module}.agda').write_text(
            source.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))


if __name__ == '__main__':
    main()
