"""Descend a relative degree chain to every opposite face, checking its polarized boundary."""
from argparse import ArgumentParser
from functools import cache
import json
from pathlib import Path

from canonical_gray_cube import build_cube
from catt import STAR, arr, check_ctx, comp2, infer, subst_tm, tdim_tm, v
from emit_agda import Emitter
from relative_coherence_based_columns import Brackets
from relative_coherence_colour_degree import add_scaled, immutable, relative_columns
from relative_coherence_cut import top_counts
from relative_coherence_head_degree import sharp_head
from relative_coherence_hidden_seam import identity
from relative_coherence_integral_degree import integral_test, loop_example
from relative_coherence_shortcut_potential import Valuation


def reduced(vector, modulus):
    if modulus:
        return {i: a % modulus for i, a in vector.items() if a % modulus}
    return {i: a for i, a in vector.items() if a}


class Transfer(Valuation):
    @cache
    def collapse(self, i, root, other):
        names = tuple(root if j == other else j for j in range(self.ctx.count(STAR)))
        return self.relabel(i, names)

    @cache
    def relabel(self, i, names):
        a = self.ctx[i]
        if a == STAR:
            return v(names[i])

        @cache
        def term(t):
            if t[0] == 'v':
                return self.relabel(t[1], names)
            return (*t[:3], tuple(term(x) for x in t[3]))
        return self.p.bracket(term(a[2]), term(a[3]))

    def project(self, vector, root, names, modulus):
        result = reduced(vector, modulus)
        for name in names:
            if name == root:
                continue
            collapsed = {}
            for i, a in result.items():
                add_scaled(collapsed, {self.collapse(i, root, name)[1]: 1}, a)
            add_scaled(result, collapsed, -1)
            result = reduced(result, modulus)
        return result

    def boundary(self, vector, modulus):
        result = {}
        for i, a in vector.items():
            s, t = self.ctx[i][2:]
            add_scaled(result, top_counts(self.ctx, t), a)
            add_scaled(result, top_counts(self.ctx, s), -a)
        return reduced(result, modulus)

    def based_representative(self, chain, point, n, emitter=None):
        """Return one bracket b and an integral witness for b - chain = boundary(w)."""
        assert n >= 2
        arrows, witness = [], {}
        for i, a in chain.items():
            if not a:
                continue
            g = v(i)
            assert tdim_tm(self.ctx, g) == n
            if a < 0:
                u, vterm = infer(self.ctx, g)[2:]
                reverse = self.p.bracket(vterm, u)
                composite = comp2(self.ctx, n-1, g, reverse)
                filler = self.p.bracket(identity(self.ctx, u), composite)
                add_scaled(witness, {filler[1]: 1}, -a)
                if emitter:
                    emitter.check_type(f'reverse{i}', self.ctx, reverse,
                                       arr(infer(self.ctx, u), vterm, u))
                    emitter.check_typed(f'cancel{i}', self.ctx, filler)
                g = reverse
            arrows.extend([self.p.base_arrow(g, point)] * abs(a))
        if arrows:
            term = arrows[0]
            for arrow in arrows[1:]:
                term = comp2(self.ctx, n-2, term, arrow)
        else:
            term = point
            for _ in range(n):
                term = identity(self.ctx, term)
        source, target = infer(self.ctx, term)[2:]
        pole = point
        for _ in range(n-2):
            pole = identity(self.ctx, pole)
        assert infer(self.ctx, source) == infer(self.ctx, target) == arr(infer(self.ctx, pole), pole, pole)
        bracket = self.p.bracket(source, target)
        comparison = self.p.bracket(term, bracket)
        add_scaled(witness, {comparison[1]: 1}, 1)
        expected = {bracket[1]: 1}
        add_scaled(expected, chain, -1)
        assert self.boundary(witness, 0) == reduced(expected, 0)
        if emitter:
            emitter.check_type('normalization', self.ctx, comparison,
                               arr(infer(self.ctx, bracket), term, bracket))
        return bracket[1], witness

    def from_identity(self, i, point, n, modulus):
        """Normalize a based bracket modulo m and return the change-of-chain witness."""
        assert n >= 2 and modulus >= 2
        a, b = self.ctx[i][2:]
        generic_unit = v(0)
        for _ in range(n-1):
            generic_unit = identity((STAR,), generic_unit)
        unit = subst_tm(generic_unit, (point,))
        to_a = self.p.bracket(unit, a)
        to_b = self.p.bracket(unit, b)
        via = comp2(self.ctx, n-1, to_a, v(i))
        triangle = self.p.bracket(via, to_b)
        product = to_b
        for _ in range(modulus-1):
            product = comp2(self.ctx, n-2, product, to_a)
        # The source of the product is a composite of m units, literally a
        # term over the singleton. Compare it with the unit by a point head.
        units = generic_unit
        for _ in range(modulus-1):
            units = comp2((STAR,), n-2, units, generic_unit)
        adjust = ('coh', (STAR,), arr(infer((STAR,), units), generic_unit, units), (point,))
        term = comp2(self.ctx, n-1, adjust, product)
        source, target = infer(self.ctx, term)[2:]
        assert source == unit
        g = self.p.bracket(unit, target)
        comparison = self.p.bracket(term, g)
        witness = {}
        for cell in (triangle, comparison):
            add_scaled(witness, {cell[1]: 1}, 1)
        expected = {g[1]: 1}
        add_scaled(expected, {i: 1}, -1)
        add_scaled(expected, {to_a[1]: 1}, -modulus)
        assert self.boundary(witness, 0) == reduced(expected, 0)
        return g[1], witness

    def descend(self, x, names, root, modulus):
        facet = tuple(i for i in names if i != root)
        boundary = self.boundary(x, modulus)
        assert all(self.names(i) < set(names) for i in boundary)
        y = {i: a for i, a in boundary.items() if self.names(i) == set(facet)}
        assert all(self.names(i) < set(facet) for i in self.boundary(y, modulus))
        primitive = self.project(x, root, names, modulus)
        cycle = self.project(y, root, names, modulus)
        assert self.boundary(primitive, modulus) == cycle
        upper_degree = sum(a*self.image(i).get(names, 0) for i, a in x.items())
        lower_degree = sum(a*self.image(i).get(facet, 0) for i, a in y.items())
        assert not reduced({0: upper_degree-(-1)**names.index(root)*lower_degree}, modulus)
        return y, primitive, cycle, lower_degree

    def normalize_filling(self, y, primitive, names, degree, modulus):
        root, facet = names[0], names[1:]
        n = len(facet)-1
        g, change = self.based_representative(y, v(facet[0]), n)
        if modulus:
            g, correction = self.from_identity(g, v(facet[0]), n, modulus)
            add_scaled(change, correction, 1)
        assert self.names(g) == set(facet)
        assert not reduced({0: self.image(g).get(facet, 0)-degree}, modulus)
        cycle = self.project({g: 1}, root, names, modulus)
        assert len(cycle) == 2**len(facet)
        filled = dict(primitive)
        add_scaled(filled, self.project(change, root, names, modulus), 1)
        assert self.boundary(filled, modulus) == cycle
        return cycle, filled


def lift(ctx, colours, p):
    labels, names = [], iter(colours)
    for a in ctx:
        labels.append(v(next(names)) if a == STAR else
                      p.bracket(*(subst_tm(t, labels) for t in a[2:])))
    return labels


def run(ctx, colours, k, descend_all=False):
    columns, d = relative_columns(ctx, colours, k)
    result = integral_test(columns, d)
    if 'potential' in result:
        print('Integral potential on this parameter:', result['potential'])
        return
    modulus = result['modulus']
    p = Brackets(k+1)
    labels = lift(ctx, colours, p)
    x = {}
    for i, a in result['chain'].items():
        add_scaled(x, {labels[i][1]: 1}, a)
    calc = Transfer(p, k)
    transfers = 0

    def visit(vec, names):
        nonlocal transfers
        if len(names) < 3:
            return
        for root in names:
            y, w, z, degree = calc.descend(vec, names, root, modulus)
            assert reduced({0: degree}, modulus)
            transfers += 1
            if len(names) == k+1:
                print(f'  omit {root}: degree {degree}, {len(y)} lower cells, '
                      f'{len(z)} absolute boundary cells, {len(w)} primitive cells')
                if root == names[0] and k >= 3:
                    normal_cycle, _ = calc.normalize_filling(y, w, names, degree, modulus)
                    print(f'  normalized opposite bracket: verified filling of its {len(normal_cycle)} signed relabellings')
            if descend_all:
                visit(y, tuple(i for i in names if i != root))
    visit(reduced(x, modulus), tuple(range(k+1)))
    check_ctx(p.ctx)
    print(f'Degree {result["degree"]}, modulus {modulus} (0 for integers), {transfers} descents.')


def basings():
    ctx, e, rev, _ = sharp_head(6)
    for root in range(7):
        p = Brackets(7)
        labels = lift(ctx, range(7), p)
        calc = Transfer(p, 6)
        forward, reverse = (subst_tm(t, labels) for t in (e, rev))
        assert not top_counts(p.ctx, forward) and not top_counts(p.ctx, reverse)
        source, target = infer(p.ctx, forward)[2:]
        assert infer(p.ctx, reverse)[2:] == (target, source)
        # At cuts 0..3 the 5-arrow's literal 4-faces are padded identically.
        a, b = p.base_pair(source, target, v(root))
        pole = v(root)
        for _ in range(4):
            pole = identity(p.ctx, pole)
        for left, right in ((a, b), (b, a)):
            pads = (p.bracket(pole, left)[1], p.bracket(right, pole)[1])
            assert len(set(pads)) == 2 and all(len(calc.names(i)) == 7 for i in pads)
            assert all(not calc.image(i).get(calc.facet, 0) for i in pads)
        check_ctx(p.ctx)
    print('Both six-arrow directions at seven basepoints: the two final 5-brackets are full and have weight zero.')


def normalization(agda):
    p = Brackets(4)
    calc = Transfer(p, 3)
    a, b, c = (p.bracket(v(i), v((i+1) % 3)) for i in range(3))
    g = p.bracket(a, a)
    h = p.bracket(comp2(p.ctx, 0, b, c), p.bracket(v(1), v(0)))
    emitter = Emitter() if agda else None
    _, w = calc.based_representative({g[1]: 2, h[1]: -1}, v(3), 2, emitter)
    calc.based_representative({}, v(0), 3)
    check_ctx(p.ctx)
    if emitter:
        agda.write_text(emitter.module(agda.stem, 'Typed reverse and signed cellular normalization.'))
    print(f'Signed rank-two chain: one based bracket and {len(w)} primitive cells. Empty rank-three chain checked.')

    p = Brackets(7)
    path = p.bracket(v(1), v(2))
    for j in range(2, 6):
        edge = p.bracket(v(j), v(j+1))
        path = comp2(p.ctx, 0, path, edge)
    # Small literal five-loop on six names, for an orbit check in the target rank.
    for _ in range(3):
        path = p.bracket(path, path)
    g = p.bracket(path, path)
    calc = Transfer(p, 6)
    orbit = calc.project({g[1]: 1}, 0, range(7), 0)
    assert len(orbit) == 64 and list(orbit.values()).count(1) == 32
    assert not calc.boundary(orbit, 0)
    check_ctx(p.ctx)
    print('Rank-five loop: 64 distinct relabellings, 32 of each sign, zero boundary and degree.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, help='typed-context JSON as in Response 19')
    parser.add_argument('--agda', type=Path, help='emit typed signed-normalization example')
    parser.add_argument('--only', choices=('descent', 'normalization', 'basings'))
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        run(immutable(data['context']), data['colours'], data['degree'])
    else:
        cols = [3, 0, 1, 0, 2, 0, 1, 0]
        if args.only in (None, 'descent'):
            run(build_cube()[0], cols, 3, True)
            run(loop_example(2, 4)[0], cols, 3, True)
        if args.only in (None, 'normalization'):
            normalization(args.agda)
        if args.only in (None, 'basings'):
            basings()
