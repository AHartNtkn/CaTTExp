"""Compute simplex degree contributed by raw operation heads from their object labels."""
from argparse import ArgumentParser
from functools import cache
import json
from pathlib import Path

from catt import (STAR, arr, comp2, infer, src, subst_tm, tdim, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_based_columns import Brackets
from relative_coherence_colour_degree import add_scaled, cone, simplex_boundary
from relative_coherence_cut import top_counts
from relative_coherence_integral_degree import loop_example
from relative_coherence_shortcut_potential import Valuation, input_terms


def difference(x, y):
    result = dict(x)
    add_scaled(result, y, -1)
    return result


def chord(a, b):
    return cone(a, {(b,): 1})


def extremes(a):
    while a[1] != STAR:
        a = a[1]
    return a[2][1], a[3][1]


def induced(arity, args, colours):
    return tuple(colours[t[1]] if a == STAR else None for a, t in zip(arity, args))


@cache
def shape_sum(t, colours, n):
    if t[0] == 'v':
        return {}
    _, arity, ty, args = t
    labels = induced(arity, args, colours)
    start, _ = extremes(ty)
    result = cone(labels[start], head_cycle(arity, ty, labels, n))
    for a, arg in zip(arity, args):
        if tdim(a)+1 == n:
            add_scaled(result, shape_sum(arg, colours, n), 1)
    return result


@cache
def head_cycle(arity, ty, colours, n):
    if n == 1:
        start, end = extremes(ty)
        result = {}
        for a in arity:
            if a != STAR:
                lo, hi = extremes(a)
                add_scaled(result, chord(colours[lo], colours[hi]), 1)
        cycle = difference(result, chord(colours[start], colours[end]))
        assert not simplex_boundary(cycle)
        return cycle
    result = difference(shape_sum(ty[2], colours, n-1), shape_sum(ty[3], colours, n-1))
    assert not simplex_boundary(result)
    return result


class Transport(Valuation):
    def colours(self):
        return tuple(i if a == STAR else None for i, a in enumerate(self.ctx))

    @cache
    def correction(self, i):
        ty = self.ctx[i]
        n = tdim(ty)+1
        if n == 1:
            return {}
        cycle = self.image(i).copy()
        add_scaled(cycle, self.primitive(ty[2], n-1), 1)
        add_scaled(cycle, self.primitive(ty[3], n-1), -1)
        assert not simplex_boundary(cycle)
        return cone(self.outer_colour(v(i)), cycle)

    def outer_colour(self, t):
        while infer(self.ctx, t) != STAR:
            t = src(self.ctx, t)
        return t[1]

    def primitive(self, t, n):
        result = shape_sum(t, self.colours(), n).copy()
        for i, count in top_counts(self.ctx, t).items():
            add_scaled(result, self.correction(i), count)
        return result

    def top_degree(self, u):
        """Check the actual signed generator counts against the syntactic formula."""
        from_counts = difference(self.primitive(src(self.ctx, u), self.r),
                                 self.primitive(tgt(self.ctx, u), self.r))
        for i, n in top_counts(self.ctx, u).items():
            cycle = self.image(i).copy()
            add_scaled(cycle, self.primitive(src(self.ctx, v(i)), self.r), 1)
            add_scaled(cycle, self.primitive(tgt(self.ctx, v(i)), self.r), -1)
            assert not simplex_boundary(cycle)
            if len(self.names(i)) <= self.k:
                assert not cycle
            add_scaled(from_counts, self.image(i), n)
            add_scaled(from_counts, cycle, -n)

        def visit(t):
            if t[0] == 'v':
                return 0
            _, arity, ty, args = t
            cycle = head_cycle(arity, ty, induced(arity, args, self.colours()), self.k-1)
            return cycle.get(self.facet, 0) + sum(visit(x) for a, x in zip(arity, args)
                                                  if tdim(a)+1 == self.k-1)
        degree = visit(u)
        expected = simplex_boundary({tuple(range(self.k+1)): degree}) if degree else {}
        assert from_counts == expected
        return degree


def sharp_head(k):
    """Build a (k-1)-head on exactly k arrows, by prefixing the preceding comparison."""
    path = tree_ctx(((),)*3)
    x, y, z = (v(2*j) for j in (1, 2, 3))
    left = comp2(path, 0, comp2(path, 0, x, y), z)
    right = comp2(path, 0, x, comp2(path, 0, y, z))
    for length in range(3, k+1):
        ty = arr(infer(path, left), left, right)
        assert infer(path, left) == infer(path, right)
        ids = tuple(map(v, range(len(path))))
        term = ('coh', path, ty, ids)
        reverse = ('coh', path, arr(ty[1], right, left), ids)
        assert infer(path, term) == ty and infer(path, reverse)[2:] == (right, left)
        colours = tuple(range(length+1))
        labels = tuple(colours[sum(a == STAR for a in path[:i])] if a == STAR else None
                       for i, a in enumerate(path))
        cycle = head_cycle(path, ty, labels, length-1)
        sign = cycle.get(tuple(range(1, length+1)), 0)
        assert abs(sign) == 1 and cycle == simplex_boundary({colours: sign})
        if length == k:
            return path, term, reverse, sign
        path = tree_ctx(((),)*(length+1))
        include = (v(1), *(v(j+2) for j in range(1, len(ids))))
        left = comp2(path, 0, v(2), subst_tm(term, include))
        right = ('coh', path, infer(path, left), tuple(map(v, range(len(path)))))


def based_check():
    ctx, _ = loop_example(2, 4)
    p = Brackets(4)
    colours = iter((3, 0, 1, 0, 2, 0, 1, 0))
    labels = []
    for a in ctx[:-1]:
        labels.append(v(next(colours)) if a == STAR else p.bracket(*(subst_tm(t, labels) for t in a[2:])))
    a, b = p.base_pair(*(subst_tm(t, labels) for t in ctx[-1][2:]), v(0))
    term = b
    for _ in range(3):
        term = comp2(p.ctx, 1, term, a)
    calc = Transport(p, 3)
    degree = calc.top_degree(term)
    assert src(p.ctx, term) == tgt(p.ctx, term)
    counts = top_counts(p.ctx, term)
    assert all(n % 4 == 0 for i, n in counts.items() if len(calc.names(i)) == 4)
    omega = sum(n*calc.image(i).get(calc.facet, 0) for i, n in counts.items())
    assert degree % 4 == omega % 4 == 2
    print(f'Based four-turn certificate: shape sum {degree}, generator weight {omega}, both 2 mod 4.')


def path_power_checks():
    path, u, _, sign = sharp_head(6)
    p = Brackets(7)
    edges = [p.bracket(v(i), v((i+1) % 7)) for i in range(7)]
    loop = edges[0]
    for edge in edges[1:]:
        loop = comp2(p.ctx, 0, loop, edge)
    calc = Transport(p, 6)
    power = loop
    for n in range(1, 8):
        coloured = [v(0)]
        for j in range(6):
            edge = comp2(p.ctx, 0, power, edges[0]) if j == 0 else edges[j]
            coloured.extend((v(j+1), edge))
        collapsed = [v(0) if a == STAR else power for a in path]
        for labels, degree in ((coloured, sign), (collapsed, 0)):
            t = subst_tm(u, labels)
            infer(p.ctx, t)
            assert len(calc.support(t)) == 7 and calc.top_degree(t) == degree
        if n < 7:
            power = comp2(p.ctx, 0, power, loop)
    print('Six-arrow head: full-support loop powers 1 through 7 preserve both root-colour predictions.')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, help='context, degree, colours and top terms as in Response 20')
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        p, terms = input_terms(data)
        calc = Transport(p, data['degree'])
        print('Structural degrees:', [calc.top_degree(t) for t in terms])
        return
    based_check()
    path_power_checks()
    for k in range(3, 8):
        path, term, reverse, sign = sharp_head(k)
        colours = list(range(k+1))
        data = dict(context=path, degree=k, colours=colours, terms=(term, reverse))
        p, terms = input_terms(data)
        calc = Transport(p, k)
        assert [calc.top_degree(t) for t in terms] == [sign, -sign]
        data['colours'] = [0, *range(k)]
        lesser, terms = input_terms(data)
        assert [Transport(lesser, k).top_degree(t) for t in terms] == [0, 0]
        print(f'{k} arrows: structural degree {sign:+} and {-sign:+}, zero after identifying two colours.')
        if k == 6 and args.agda:
            out = Emitter()
            for name, t in [('unitDegree', term), ('reverseUnitDegree', reverse)]:
                out.check_type(name, path, t, infer(path, t))
            args.agda.write_text(out.module(args.agda.stem, 'Opposite structural degrees on six arrows.'))


if __name__ == '__main__':
    main()
