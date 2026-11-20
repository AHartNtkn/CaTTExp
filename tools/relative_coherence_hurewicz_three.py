"""Check the degree-three cellular Hurewicz formula and a family of torsion presentations."""
from argparse import ArgumentParser
from collections import Counter
from itertools import combinations
from math import gcd
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, disc_tree, infer, sub_from, subst_ty,
                  tdim, tree_ctx, v)
from ct_suspension import ident, susp_ctx, susp_tm, susp_ty
from emit_agda import Emitter
from gray_globe_branch_comparisons import cylinder
from relative_coherence_based_columns import Brackets
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head
from relative_coherence_hom_chains import boundary as hom_boundary
from relative_coherence_walking_graph import template


def difference(ctx, a, b):
    value = top_counts(ctx, b)
    value.subtract(top_counts(ctx, a))
    return value


def chain_formula(output):
    disk = tree_ctx(disc_tree(3))
    old = disk + (disk[-1],)
    full, minus, mix = cylinder(old, set(range(len(old))))
    plus = [v(x[1] + 1) for x in minus]
    p = Brackets(5)
    values = []
    point = (STAR,)
    for i, ty in enumerate(old):
        rank = tdim(ty) + 1
        for role, slot in [('minus', minus[i]), ('plus', plus[i]), ('change', mix[i])]:
            assert slot == v(len(values))
            actual = subst_ty(full[slot[1]], values)
            if actual == STAR:
                value = v(0 if role == 'minus' else 1 + i % 4)
            elif role == 'minus' and rank <= 2:
                a, b = actual[2:]
                value = head(point, a, b)
                if i % 2:
                    value = comp2(point, rank-1, ident(point, a), value)
            else:
                a, b = actual[2:]
                value = p.bracket(a, b)
                if rank == 3 and i == len(disk):
                    d = tdim(actual)
                    value = comp2(p.ctx, d, ident(p.ctx, a), value)
            assert infer(p.ctx, value) == actual
            values.append(value)
    residuals = []
    for i, ty in enumerate(old):
        h = values[mix[i][1]]
        a, b = infer(p.ctx, h)[2:]
        expected = difference(p.ctx, values[minus[i][1]], values[plus[i][1]])
        if ty != STAR:
            s, t = (x[1] for x in ty[2:])
            expected.update(top_counts(p.ctx, values[mix[s][1]]))
            expected.subtract(top_counts(p.ctx, values[mix[t][1]]))
        assert difference(p.ctx, a, b) == expected
        if tdim(ty) == 2:
            residual = difference(p.ctx, a, b)
            residual.subtract(difference(p.ctx, values[minus[i][1]], values[plus[i][1]]))
            residuals.append(residual)
            if output:
                output.check_type('adaptive'+str(i), p.ctx, h, subst_ty(full[mix[i][1]], values))
    assert len(residuals) == 2 and residuals[0] == residuals[1] and +residuals[0]


def biarrow(ctx, a, b):
    k = tdim(infer(ctx, a)) + 1
    work = template(k, 4)
    sigma = list(sub_from(work.ctx[:work.old+1], ctx, {work.old: a}))
    assert infer(ctx, b) == subst_ty(work.ctx[work.duplicate], sigma)
    sigma.append(b)
    types = []
    for ty in work.ctx[work.forward:]:
        types.append(subst_ty(ty, sigma))
        sigma.append(v(len(ctx)+len(types)-1))
    return ctx + tuple(types), sigma[work.forward], sigma[work.forward+1]


def determinant(a, b, c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0])
            + a[2]*(b[0]*c[1]-b[1]*c[0]))


def torsion(m, output):
    ctx = (STAR,)
    pole = ident(ctx, ident(ctx, v(0)))
    ctx, g, inverse = biarrow(ctx, pole, pole)
    unit = ident(ctx, pole)
    power = g
    for _ in range(1, m):
        power = comp2(ctx, 2, power, g)
    ctx, kill, restore = biarrow(ctx, power, unit)
    check_ctx(ctx)
    rows = [i for i, ty in enumerate(ctx) if tdim(ty) == 2]
    assert len(rows) == 3
    cols = []
    for ty in ctx:
        if tdim(ty) == 3:
            column = difference(ctx, *ty[2:])
            cols.append(tuple(column[r] for r in rows))
    minor1 = gcd(*(a for col in cols for a in col))
    minor2 = gcd(*(a[i]*b[j]-a[j]*b[i] for a,b in combinations(cols, 2)
                   for i,j in combinations(range(3), 2)))
    minor3 = gcd(*(determinant(*triple) for triple in combinations(cols, 3)))
    assert (minor1, minor2, minor3) == (1, 1, m)
    for k in (0, 1, 5):
        tail = unit
        for _ in range(k):
            tail = comp2(ctx, 2, tail, inverse)
        for name, term, start, end, sign in [('kill', kill, power, unit, -1),
                                              ('restore', restore, unit, power, 1)]:
            whiskered = comp2(ctx, 2, term, tail)
            a, b = comp2(ctx, 2, start, tail), comp2(ctx, 2, end, tail)
            expected = arr(infer(ctx, a), a, b)
            assert infer(ctx, whiskered) == expected
            assert difference(ctx, a, b) == Counter({g[1]: sign*m})
            lifted = susp_tm(whiskered)
            ambient = susp_ctx(ctx)
            assert infer(ambient, lifted) == susp_ty(expected)
            assert hom_boundary(ambient, lifted) == {susp_tm(g): sign*m}
            if output and k == 5:
                output.check_type(name, ctx, whiskered, expected)
                output.check_type(name + 'Susp', ambient, lifted, susp_ty(expected))
    return len(cols)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    chain_formula(emitter)
    ncols = sum(torsion(m, emitter if m == 3 else None) for m in range(1, 13))
    print(f'Adaptive boundary formula at eight slots; 12 torsion presentations, {ncols} '
          'four-columns, all determinantal divisors, and 72 directed typed whiskerings.')
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Adaptive four-caps and torsion columns in both directions.'))
