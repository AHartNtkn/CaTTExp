"""Type-check the cap changes and endpoint panels for polygon suspension transfer."""
import argparse
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, fv_ty, infer, maximal_vars, restrict,
                  sub_from, subst_tm, subst_ty, tree_ctx, v)
from ct_suspension import build, ident, susp_ty
from emit_agda import Emitter


def faces(context, top, degree):
    terms = {('g', degree, '*'): top}
    for d in reversed(range(degree)):
        a, b = infer(context, top)[2:]
        terms['g', d, '-'] = a
        terms['g', d, '+'] = b
        top = a
    return terms


def generic_filler(context, wanted, maximal):
    support = {t[1] for t in maximal}
    for i in reversed(range(len(context))):
        if i in support:
            support.update(fv_ty(context[i]))
    arity, inclusion = restrict(context, support)
    renaming = {i: v(j) for j, i in enumerate(sorted(support))}
    generic_type = subst_ty(wanted, renaming)
    term = ('coh', arity, generic_type, inclusion)
    assert infer(context, term) == wanted
    return term


def check(level, mode, emitter):
    # The central (q+1)-globe supplies the suspended P variable and its faces.
    globe = disc_tree(level.k + 1)
    left = mode in ('bridge-left', 'hidden-left')
    hidden = mode.startswith('hidden')
    if hidden:
        tree = disc_tree(2) + globe if left else globe + disc_tree(2)
    else:
        tree = ((),) + globe + ((),)
    G = tree_ctx(tree)
    maximal = [v(i) for i in maximal_vars(G)]
    if hidden:
        polygon, center = maximal if left else maximal[::-1]
        branch = infer(G, polygon)[2:]
    else:
        prefix, center, suffix = maximal
    labels = faces(G, center, level.k)
    source, target = v(0), infer(G, maximal[-1])
    while target[1] != STAR:
        target = target[1]
    target = target[3]
    sub = [source, target]
    ends = {i: pair for pair, i in level.end.items()}
    mixed = {i: g for g, i in level.mix.items()}
    for i, A in enumerate(level.G):
        wanted = subst_ty(susp_ty(A), sub)
        if i in ends:
            side, g = ends[i]
            p = labels[g]
            if hidden:
                t = comp2(G, 0, branch[side], p) if left else comp2(G, 0, p, branch[side])
            else:
                canonical = comp2(G, 0, prefix, comp2(G, 0, p, suffix))
                bracketed = comp2(G, 0, comp2(G, 0, prefix, p), suffix)
                if left:
                    padded = comp2(G, 0, ident(G, source), bracketed)
                    t = padded if side == 0 else canonical
                else:
                    padded = comp2(G, 0, bracketed, ident(G, target))
                    t = canonical if side == 0 else padded
                assert padded != canonical
        else:
            g = mixed[i]
            p = labels[g]
            support = (polygon, p) if hidden else (prefix, p, suffix)
            t = generic_filler(G, wanted, support)
            if emitter is not None and g[2] == '*':
                emitter.check_type(f'{mode}-{level.k}', G, t, wanted)
        assert infer(G, t) == wanted
        sub.append(t)
    if hidden:
        # Instantiate the generic 2-globe by a polygon variable with composite
        # boundary paths of lengths two and three.
        data = [STAR] * 5
        routes = []
        for route in ((0, 1, 4), (0, 2, 3, 4)):
            edges = []
            for a, b in zip(route, route[1:]):
                edges.append(v(len(data)))
                data.append(arr(STAR, v(a), v(b)))
            path = edges[-1]
            for edge in reversed(edges[:-1]):
                path = comp2(tuple(data), 0, edge, path)
            routes.append(path)
        poly = v(len(data))
        data.append(arr(infer(tuple(data), routes[0]), *routes))
        position = v(4 if left else 0)
        other = v(len(data))
        data.append(STAR)
        a, b = (position, other) if left else (other, position)
        A = arr(STAR, a, b)
        for _ in range(level.k):
            a, b = v(len(data)), v(len(data) + 1)
            data.extend((A, A))
            A = arr(A, a, b)
        z = v(len(data))
        data.append(A)
        dest = tuple(data)
        sigma = sub_from(G, dest, {polygon[1]: poly, center[1]: z})
        result, expected = subst_tm(t, sigma), subst_ty(wanted, sigma)
        assert infer(dest, result) == expected
        if emitter is not None:
            emitter.check_type(f'{mode}-polygon-{level.k}', dest, result, expected)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('degree', type=int, help='maximum degree before suspension')
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    for level in build(args.degree):
        for mode in ('bridge-left', 'bridge-right', 'hidden-left', 'hidden-right'):
            check(level, mode, emitter)
        print(f'Disk degree {level.k}: both cap changes and both polygon panels type-check')
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Polygon suspension panels.'))
