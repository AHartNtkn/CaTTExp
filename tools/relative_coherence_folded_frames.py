"""Fold anchored degree equations onto their boundary and compare facet coefficients."""
from argparse import ArgumentParser
from functools import cache
from itertools import permutations
import json
from pathlib import Path

from catt import (STAR, arr, coh_between, comp2, disc_tree, infer, maximal_vars, ps_boundary_vars,
                  ps_dim, restrict, src, sub_from, subst_tm, subst_ty, tdim, tgt, tree_ctx, ucomp, v)
from emit_agda import Emitter
from partial_cylinder_steiner import trees
from relative_coherence_based_columns import Brackets
from relative_coherence_colour_degree import add_scaled, simplex_boundary
from relative_coherence_hidden_seam import identity
from relative_coherence_shortcut_potential import Valuation, frame_test, input_terms


def fold(arity, r):
    """The top strings fold to their negative endpoint, leaving lower slots fixed."""
    if ps_dim(arity) <= r:
        labels = tuple(map(v, range(len(arity))))
        return arity, labels, list(range(len(arity)))
    assert ps_dim(arity) == r+1
    keep = sorted(ps_boundary_vars(arity, r, '-'))
    base, _ = restrict(arity, set(keep))
    ids = {i: v(j) for j, i in enumerate(keep)}
    predecessor = {a[3][1]: a[2][1] for a in arity if tdim(a)+1 == r+1}
    labels = []
    for i, a in enumerate(arity):
        if tdim(a)+1 == r+1:
            term = identity(base, labels[a[2][1]])
        else:
            j = i
            while j in predecessor:
                j = predecessor[j]
            term = ids[j]
        assert infer(base, term) == subst_ty(a, labels)
        labels.append(term)
    return base, tuple(labels), keep


def flatten_pair(base, t, args):
    flat = ('coh', base, infer(base, t), tuple(map(v, range(len(base)))))
    assert infer(base, flat) == infer(base, t)
    return tuple(subst_tm(('coh', base, arr(infer(base, t), a, b),
                           tuple(map(v, range(len(base))))), args)
                 for a, b in ((t, flat), (flat, t)))


def folded_equation(val, u):
    _, arity, ty, args = val.anchored_head(u)
    base, q, keep = fold(arity, val.r)
    original = args
    args = tuple(original[i] for i in keep)
    pairs = []
    for t in ty[2:]:
        lifted = subst_tm(t, q)
        assert subst_tm(lifted, args) == subst_tm(t, original)
        pair = flatten_pair(base, lifted, args)
        for side in pair:
            infer(val.ctx, side)
        pairs.append(pair)
    assert tgt(val.ctx, pairs[0][0]) == tgt(val.ctx, pairs[1][0])
    difference = val.equation(pairs[0][0]).copy()
    add_scaled(difference, val.equation(pairs[1][0]), -1)
    assert difference == val.equation(u)
    return pairs


class Facets(Valuation):
    @cache
    def frames(self, t):
        if t[0] == 'v':
            return {}
        _, arity, ty, args = t
        labels = list(args)
        result = {}
        for i, a in enumerate(arity):
            if tdim(a)+1 == self.r:
                add_scaled(result, self.frames(args[i]), 1)
                labels[i] = self.anchor(args[i])
        frame = ('coh', arity, ty, tuple(labels))
        add_scaled(result, {frame: 1}, 1)
        return result

    @cache
    def filling(self, frame):
        return self.bracket_image(self.anchor(frame), frame)

    def gauges(self, u):
        relation = {}
        for side, sign in [(u, 1)] + [(x, -1) for a, x in zip(u[1], u[3])
                                      if tdim(a)+1 == self.r+1]:
            add_scaled(relation, self.frames(tgt(self.ctx, side)), sign)
            add_scaled(relation, self.frames(src(self.ctx, side)), -sign)
        proper, full = {}, {}
        for frame, n in relation.items():
            table = full if len(self.support(frame)) == self.k+1 else proper
            add_scaled(table, self.filling(frame), n)
        total = proper.copy()
        add_scaled(total, full, 1)
        assert not simplex_boundary(total)
        affine = self.equation(u)
        assert total.get(self.facet, 0) == affine.get(None, 0)
        values = []
        for i in range(self.k+1):
            facet = tuple(j for j in range(self.k+1) if i != j)
            sign = (-1)**i
            def beta(frame):
                return -sign*self.filling(frame).get(facet, 0)
            evaluated = affine.get(None, 0) + sum(n*beta(f) for f, n in affine.items() if f is not None)
            assert evaluated == sign*proper.get(facet, 0)
            values.append(evaluated)
        return values


def arity_checks(limit):
    counts = {}
    for n in range(1, limit+1):
        for tree in trees(n):
            arity = tree_ctx(tree)
            height = ps_dim(arity)
            if not 2 <= height <= 5:
                continue
            r = height-1
            p = Brackets(r+3)
            val = Facets(p, r+2)
            labels, index = [], 0
            for a in arity:
                if a == STAR:
                    labels.append(v(index % (r+3)))
                    index += 1
                else:
                    labels.append(p.bracket(*subst_ty(a, labels)[2:]))
            a = infer(arity, ucomp(arity))
            # An extra literal unit on the negative face tests a nonstandard head.
            s = comp2(arity, r-1, identity(arity, src(arity, a[2])), a[2])
            u = ('coh', arity, arr(a[1], s, a[3]), tuple(labels))
            infer(p.ctx, u)
            folded_equation(val, u)
            val.gauges(u)
            counts[height] = counts.get(height, 0)+1
    print('Labelled arities by height:', counts)


def unit_routes(k, agda):
    p = Brackets(k+1)
    val = Facets(p, k)
    g = p.bracket(v(k-1), v(k))
    for j in range(k-2, 1, -1):
        edge = p.bracket(v(j), v(j+1))
        w = comp2(p.ctx, 0, edge, g)
        g = p.bracket(val.anchor(w), w)
    edge, last = p.bracket(v(1), v(2)), p.bracket(v(k), v(0))
    tree = ((), disc_tree(k-3), ())
    arity = tree_ctx(tree)
    slots = [v(i) for i in maximal_vars(arity)]
    args = sub_from(arity, p.ctx, dict(zip(maximal_vars(arity), (edge, g, last))))
    w = comp2(arity, 0, slots[0], slots[1])
    left = comp2(arity, 0, w, slots[2])
    middle = comp2(arity, k-3, identity(arity, src(arity, left)), left)
    right = ('coh', arity, infer(arity, left), tuple(map(v, range(len(arity)))))
    out = Emitter() if agda else None
    results = {}
    for i, j in permutations(range(3), 2):
        terms = (left, middle, right)
        u = subst_tm(coh_between(arity, tree, slots, terms[i], terms[j]), args)
        ty = arr(infer(p.ctx, subst_tm(terms[i], args)), subst_tm(terms[i], args),
                 subst_tm(terms[j], args))
        assert infer(p.ctx, u) == ty
        gauge = val.gauges(u)
        assert gauge[1] == 0 and (k == 3 or not any(gauge[1:]))
        results[i,j] = val.equation(u)
        if out:
            out.check_type(f'route{i}to{j}', p.ctx, u, ty)
    split = results[0,1].copy()
    add_scaled(split, results[1,2], 1)
    assert split == results[0,2] and results[0,2].get(None) == -1
    print(f'Rank {k}: six directed comparisons, facet residuals for the direct route: '
          f'{val.gauges(subst_tm(coh_between(arity, tree, slots, left, right), args))}.')
    if out:
        agda.write_text(out.module(agda.stem, 'Both directions of the three flattening comparisons.'))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--edges', type=int, default=6)
    parser.add_argument('--agda', type=Path)
    parser.add_argument('--input', type=Path, help='head-equation JSON from Response 20')
    opts = parser.parse_args()
    if opts.input:
        data = json.loads(opts.input.read_text())
        p, terms = input_terms(data)
        val = Facets(p, data['degree'])
        folded = [pair[0] for u in terms for pair in folded_equation(val, u)]
        gauges = [val.gauges(u) for u in folded]
        print('Common zero facets:', [i for i in range(val.k+1) if all(g[i] == 0 for g in gauges)])
        print('Folded system:', frame_test(val, folded))
    else:
        arity_checks(opts.edges)
        for k in range(3, 7):
            unit_routes(k, opts.agda if k == 6 else None)
