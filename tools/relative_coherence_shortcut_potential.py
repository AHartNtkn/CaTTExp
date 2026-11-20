"""Integrate bracket and globular-composition weights on arbitrary literal slot frames."""
from argparse import ArgumentParser
from functools import cache
from itertools import product
import json
from pathlib import Path

from canonical_gray_cube import build_cube
from catt import (STAR, arr, check_ctx, coh_between, comp2, disc_tree, fv_tm, fv_ty,
                  infer, maximal_vars, src, subst_tm, subst_ty, sub_from, tdim, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_based_columns import Brackets
from relative_coherence_colour_degree import add_scaled, cone, immutable
from relative_coherence_cut import top_counts
from relative_coherence_integral_degree import integral_test, interval_parameter


class Valuation:
    def __init__(self, brackets, k):
        self.p = brackets
        self.k = k
        self.r = k - 2
        self.facet = tuple(range(1, k+1))

    @property
    def ctx(self):
        return self.p.ctx

    @cache
    def names(self, i):
        ty = self.ctx[i]
        return {i} if ty == STAR else set().union(*(self.names(j) for j in fv_ty(ty)))

    def support(self, t):
        return set().union(*(self.names(i) for i in fv_tm(t)))

    @cache
    def image(self, i):
        if self.ctx[i] == STAR:
            return {(i,): 1}
        s, t = self.ctx[i][2:]
        return self.bracket_image(s, t)

    def bracket_image(self, s, t):
        counts = top_counts(self.ctx, t)
        counts.subtract(top_counts(self.ctx, s))
        boundary = {}
        for j, n in counts.items():
            if n:
                add_scaled(boundary, self.image(j), n)
        return cone(min(self.support(s) | self.support(t)), boundary)

    def anchor(self, t):
        return self.p.bracket(src(self.ctx, t), tgt(self.ctx, t))

    def basic(self, t):
        if len(self.support(t)) == self.k+1 or t[0] == 'v':
            return 0
        return self.bracket_image(self.anchor(t), t).get(self.facet, 0)

    @cache
    def affine(self, t):
        assert tdim(infer(self.ctx, t))+1 == self.r
        if t[0] == 'v':
            return {}
        _, arity, ty, args = t
        slots = [i for i, a in enumerate(arity) if tdim(a)+1 == self.r]
        anchored = list(args)
        for i in slots:
            anchored[i] = self.anchor(args[i])
        base = ('coh', arity, ty, tuple(anchored))
        assert infer(self.ctx, t) == infer(self.ctx, base)
        if len(self.support(base)) == self.k+1:
            result = {base: 1}
        else:
            constant = self.basic(base)
            result = {None: constant} if constant else {}
        for i in slots:
            add_scaled(result, self.affine(args[i]), 1)
        if len(self.support(t)) <= self.k:
            assert set(result) <= {None} and result.get(None, 0) == self.basic(t)
        return result

    def value(self, t):
        return self.affine(t).get(None, 0)

    def equation(self, u):
        _, arity, _, args = u
        result = {}
        for t, sign in [(u, 1)] + [(arg, -1) for a, arg in zip(arity, args)
                                   if tdim(a)+1 == self.r+1]:
            add_scaled(result, self.affine(tgt(self.ctx, t)), sign)
            add_scaled(result, self.affine(src(self.ctx, t)), -sign)
        return result

    def anchored_head(self, u):
        _, arity, ty, args = u
        labels = []
        for a, arg in zip(arity, args):
            dim = tdim(a)+1
            if dim == self.r:
                arg = self.anchor(arg)
            elif dim == self.r+1:
                arg = self.p.bracket(*subst_ty(a, labels)[2:])
            labels.append(arg)
        result = ('coh', arity, ty, tuple(labels))
        infer(self.ctx, result)
        return result

    def weight(self, u):
        residual = 0
        for g, n in top_counts(self.ctx, u).items():
            weight = self.image(g).get(self.facet, 0)
            change = self.value(tgt(self.ctx, v(g))) - self.value(src(self.ctx, v(g)))
            if len(self.names(g)) <= self.k:
                assert weight == change
            else:
                residual += n*(weight-change)
        return residual

    def defect(self, u):
        omega = sum(n*self.image(g).get(self.facet, 0)
                    for g, n in top_counts(self.ctx, u).items())
        change = self.value(tgt(self.ctx, u)) - self.value(src(self.ctx, u))
        return omega - self.weight(u) - change


def samples(k):
    p, tops = interval_parameter(k)
    val = Valuation(p, k)
    checked = set()
    for col in tops:
        pair = p.ctx[col[1]][2:]
        for u in pair:
            assert val.defect(u) == 0
            checked.add(u)
    # Compose pairs of based routes at all lower cuts. Identical outside factors
    # may contain arbitrary generators, including full-colour loops.
    a, b = p.base_pair(*p.ctx[tops[0][1]][2:], v(0))
    loop = p.bracket(src(p.ctx, a), src(p.ctx, a))
    for power in range(1, 5):
        for cut in range(k-1):
            for x, y in product((a,b), repeat=2):
                u = comp2(p.ctx, cut, comp2(p.ctx, cut, x, loop), y)
                assert val.defect(u) == 0
                checked.add(u)
        loop = comp2(p.ctx, k-2, loop, loop)
    print(f'Rank {k}: {len(tops)} shortcut columns, {len(checked)} distinct typed sides and composites.')


def flatten(k, agda):
    p = Brackets(k+1)
    val = Valuation(p, k)
    # Extend the positive interval at its least colour each time.
    g = p.bracket(v(k-1), v(k))
    for j in range(k-2, 1, -1):
        prefix = p.bracket(v(j), v(j+1))
        w = comp2(p.ctx, 0, prefix, g)
        g = p.bracket(val.anchor(w), w)
    edge = p.bracket(v(1), v(2))
    last = p.bracket(v(k), v(0))
    tree = ((), disc_tree(k-3), ())
    arity = tree_ctx(tree)
    slots = [v(i) for i in maximal_vars(arity)]
    nested = comp2(arity, 0, comp2(arity, 0, slots[0], slots[1]), slots[2])
    flat = ('coh', arity, infer(arity, nested), tuple(v(i) for i in range(len(arity))))
    assert flat != nested and infer(arity, nested) == infer(arity, flat)
    args = sub_from(arity, p.ctx, dict(zip(maximal_vars(arity), (edge, g, last))))
    expected = [subst_tm(t, args) for t in (nested, flat)]
    results = []
    for label, left, right in (('flatten', nested, flat), ('reverseFlatten', flat, nested)):
        generic = coh_between(arity, tree, slots, left, right)
        u = subst_tm(generic, args)
        a, b = expected if left == nested else reversed(expected)
        ty = arr(infer(p.ctx, a), a, b)
        assert infer(p.ctx, u) == ty and not top_counts(p.ctx, u)
        results.append((label, u, ty, val.defect(u)))
    assert [r[3] for r in results] == [1, -1]
    relation = val.equation(results[0][1])
    assert relation == val.equation(val.anchored_head(results[0][1]))
    assert relation.get(None) == -1
    assert relation == {key: -x for key, x in val.equation(results[1][1]).items()}
    print(f'Rank {k}: opposite unit defects, one affine equation with {len(relation)-1} unknowns.')
    if agda:
        out = Emitter()
        for label, u, ty, _ in results:
            out.check_type(label, p.ctx, u, ty)
        agda.write_text(out.module(agda.stem, 'Structural flattening in both directions.'))


def frame_test(val, terms):
    frames, columns, constants = {}, {}, {}
    for j, u in enumerate(terms):
        assert u[0] == 'coh' and tdim(infer(val.ctx, u))+1 == val.k-1
        relation = val.equation(val.anchored_head(u))
        assert relation == val.equation(u)
        columns[j] = {frames.setdefault(key, len(frames)): x
                      for key, x in relation.items() if key is not None}
        constants[j] = -relation.get(None, 0)
    return integral_test(columns, constants)


def input_terms(data):
    ctx = immutable(data['context'])
    check_ctx(ctx)
    k, colours = data['degree'], data['colours']
    if k < 3 or len(colours) != ctx.count(STAR) or not set(colours) <= set(range(k+1)):
        raise ValueError('expected degree >= 3 and one simplex colour per object')
    names = iter(colours)
    p, labels = Brackets(k+1), []
    for ty in ctx:
        labels.append(v(next(names)) if ty == STAR else p.bracket(*subst_ty(ty, labels)[2:]))
    terms = immutable(data['terms'])
    for u in terms:
        if u[0] != 'coh' or tdim(infer(ctx, u))+1 != k-1:
            raise ValueError('expected coherence-headed terms of dimension degree-1')
    return p, [subst_tm(u, labels) for u in terms]


def from_input(data):
    p, terms = input_terms(data)
    return frame_test(Valuation(p, data['degree']), terms)


def cube_equations():
    cube, _ = build_cube()
    ctx = cube[:-1]
    nodes = set()
    def visit(t):
        if t[0] == 'coh' and t not in nodes and tdim(infer(ctx, t))+1 == 2:
            nodes.add(t)
            for arg in t[3]:
                visit(arg)
    for t in cube[-1][2:]:
        visit(t)
    data = {'context': ctx, 'degree': 3, 'terms': sorted(nodes),
            'colours': [min([3] + [j for j in range(3) if x >> j & 1]) for x in range(8)]}
    result = from_input(data)
    assert len(nodes) == 22 and result['modulus'] == 0 and abs(result['degree']) == 1
    print(f'Three-cube: 22 head equations give {result}.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path, help='emit both rank-five judgements for seven colours')
    parser.add_argument('--input', type=Path, help='typed context JSON with an additional terms array')
    args = parser.parse_args()
    if args.input:
        print(from_input(json.loads(args.input.read_text())))
    else:
        cube_equations()
        for rank in range(3, 7):
            flatten(rank, args.agda if rank == 6 else None)
            samples(rank)
