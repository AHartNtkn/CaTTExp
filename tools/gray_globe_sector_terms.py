"""Check the CaTT section in the crossing hom away from rank pair (2,2)."""
import argparse
from collections import Counter
from functools import cache
from itertools import product
from pathlib import Path

from canonical_gray_two_discs import strict_interpreter
from catt import (STAR, arr, check_ctx, comp2, glue_tree, infer,
                  maximal_vars, sub_from, subst_tm, subst_ty, tree_ctx, v)
from ct_suspension import susp_tm, susp_ty
from emit_agda import Emitter
from gray_globe_comparison import CORNERS, atom, face, globe
from gray_globe_factorizations import hole_split, profile
from gray_globe_section import cells, row_map
from rc2 import reassoc


def arrow(ctx, s, t):
    ty = infer(ctx, s)
    assert ty == infer(ctx, t)
    return arr(ty, s, t)


def pure_type(ctx, names, g):
    if sum(d for d, _ in g) == 0:
        return STAR
    return arrow(ctx, *(names[face(atom(g), side)[-1][0][0]] for side in (0, 1)))


@cache
def tile(m, axis):
    """The ordinary one-sided suspension transfer, with disk in slot axis."""
    def basis(p, t):
        return (p, t) if axis == 0 else (t, p)

    shape = (m, 1) if axis == 0 else (1, m)
    ctx, names = (), {}

    def declare(g, ty):
        nonlocal ctx
        names[g] = v(len(ctx))
        ctx += (ty,)
        return names[g]

    for g in sorted(product(*(globe(d) for d in shape)), key=lambda g: sum(d for d, _ in g)):
        if not all(d for d, _ in g):
            declare(g, pure_type(ctx, names, g))
    terms = {atom(g): t for g, t in names.items()}
    if m:
        old, labels, lower = tile(m-1, axis)
        sigma = [names[((0, 0), (0, 0))], names[((0, 1), (0, 1))]]
        for g, ty in zip(labels, old):
            p, t = g[axis], g[1-axis]
            sp = p[0]+1, p[1]
            wanted = subst_ty(susp_ty(ty), sigma)
            if t[0]:
                image = declare(basis(sp, t), wanted)
            else:
                i = t[1]
                layer = i if axis else 1-i
                pole = 1-i if axis else i
                cap = names[basis(sp, (0, layer))]
                edge = names[basis((0, pole), (1, 2))]
                image = comp2(ctx, 0, edge, cap) if layer else comp2(ctx, 0, cap, edge)
            assert infer(ctx, image) == wanted
            sigma.append(image)

        def desuspend(g):
            (rank, tag), time = g[axis], g[1-axis]
            if rank:
                if not axis and not time[0]:
                    time = (0, 1-time[1])
                return basis((rank-1, tag), time)

        for c in cells(shape):
            if c and c[0] == CORNERS:
                terms[c] = subst_tm(susp_tm(lower[row_map(c, 1, desuspend)]), sigma)
    assert terms.keys() == cells(shape)-{()}
    assert all(terms[atom(g)] == t for g, t in names.items())
    return ctx, tuple(names), terms


def edge_context(m, n):
    """Identify the four tile contexts on their common ordinary squares."""
    ctx, names, terms = (), {}, {}
    for disk, other, axis in ((m, n, 0), (n, m, 1)):
        local, generators, chosen = tile(disk, axis)
        for label in (t for t in globe(other) if t[0] == 1):
            def embed(g):
                result = list(g)
                if result[1-axis][0]:
                    result[1-axis] = label
                return tuple(result)

            sigma = []
            for g, ty in zip(generators, local):
                h = embed(g)
                wanted = subst_ty(ty, sigma)
                if h not in names:
                    names[h] = v(len(ctx))
                    ctx += (wanted,)
                assert infer(ctx, names[h]) == wanted
                sigma.append(names[h])
            for c, t in chosen.items():
                h, image = row_map(c, 0, embed), subst_tm(t, sigma)
                if h in terms:
                    assert terms[h] == image
                terms[h] = image
    check_ctx(ctx)
    return ctx, names, terms


def boundary_bridge(ctx, evaluate, names, source, target):
    """Compare the two orders and bracketings of the three corner 2-steps."""
    def unpack(t, leaves):
        # A cut-one binary composite has two maximal 2-slots in its arity.
        if t[0] == 'coh' and t[1] == tree_ctx(glue_tree(2, 1, 2)):
            return [unpack(t[3][i], leaves) for i in maximal_vars(t[1])]
        leaves.append(t)
        return len(leaves)-1

    left, right = [], []
    ls, rs = unpack(source, left), unpack(target, right)
    assert len(left) == len(right) == 3
    if left == right:
        return reassoc(ctx, left, ls, rs)[0]
    square, = (t for t in left if t[0] == 'v')
    before = left[-1] == square
    assert (right[-1] == square) == before
    pair = left[:2] if before else left[1:]
    other_pair = right[:2] if before else right[1:]
    grouping = [[0, 1], 2] if before else [0, [1, 2]]
    first = reassoc(ctx, left, ls, grouping)[0]
    last = reassoc(ctx, right, grouping, rs)[0]

    # The two independent pure 2-generators live on a horizontal wedge.
    # Recover each route and perform the exchange on its globular arity.
    P = tree_ctx(glue_tree(2, 0, 2))
    tops = maximal_vars(P)
    bases = [evaluate(t)[-1][0][0] for t in pair]
    for order in (bases, bases[::-1]):
        # The terminal object of the first pure variable is the initial
        # object of the second in the actual diagonal path.
        if atom(order[0])[0][1] == atom(order[1])[0][0]:
            break
    else:
        raise ValueError("The two corner changes do not share an object")
    sigma = sub_from(P, ctx, {i: names[g] for i, g in zip(tops, order)})
    rename = {t[1]: v(i) for i, t in enumerate(sigma)}
    a, b = [subst_tm(comp2(ctx, 1, *ps), rename) for ps in (pair, other_pair)]
    exchange = ('coh', P, arrow(P, a, b), sigma)
    middle = comp2(ctx, 1, exchange, square) if before else comp2(ctx, 1, square, exchange)
    path = [t for t in (first, middle, last) if t is not None]
    result = path[0]
    for t in path[1:]:
        result = comp2(ctx, 2, result, t)
    assert infer(ctx, result) == arrow(ctx, source, target)
    return result


def verify(m, n, emitter):
    ctx, names, chosen = edge_context(m, n)
    evaluate = strict_interpreter(ctx, tuple(names))
    poles = atom(((m, 2), (n, 2)))[:2]
    domain = {c for c in cells((m,n)) if c[:2] == poles and (2,2) not in profile(c)}
    comparisons = {}

    def paste(c, hole):
        (x, y), = hole_split(c, *hole)
        return comp2(ctx, sum(hole)-2, chosen[x], chosen[y])

    def corner(c, side):
        row = c[2][side]
        return c[:2] + ((row, row),)

    def bridge(c, side):
        z = corner(c, side)
        if (z, side) not in comparisons:
            ends = [chosen[z], paste(z, (2, 1))]
            if side:
                ends.reverse()
            comparisons[z, side] = boundary_bridge(ctx, evaluate, names, *ends)
        return comparisons[z, side]

    cases = Counter()
    emitted = set()
    for c in sorted(domain, key=lambda x: (len(x), len(profile(x)), x)):
        ranks = profile(c)
        if (1, 2) not in ranks:
            term, case = paste(c, (1, 2)), 'A'
        elif (2, 1) not in ranks:
            term, case = paste(c, (2, 1)), 'B'
            first, last = bridge(c, 0), bridge(c, 1)
            if first is not None:
                term = comp2(ctx, 2, first, term)
            if last is not None:
                term = comp2(ctx, 2, term, last)
        else:
            term, case = paste(c, (2, 2)), 'route'
        wanted = arrow(ctx, *(chosen[face(c, s)] for s in (0, 1)))
        assert infer(ctx, term) == wanted and evaluate(term) == c
        chosen[c] = term
        cases[case] += 1
        if emitter is not None and (case, len(c)) not in emitted:
            emitter.check_type(f'sector-{case}-{len(c)-1}', ctx, term, wanted)
            emitted.add((case, len(c)))
    print(f'Checked all {len(domain)} crossing-sector terms: {dict(cases)}')
    return ctx, names, chosen


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if min(args.m, args.n) < 2:
        parser.error('both globe dimensions must be at least two')
    emitter = Emitter() if args.agda else None
    verify(args.m, args.n, emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'From tools/gray_globe_sector_terms.py.'))
