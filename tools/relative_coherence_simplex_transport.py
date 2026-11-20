"""Track simplex flips and certify local inverse data in the bracket computad."""
from argparse import ArgumentParser
from collections import Counter, deque
from functools import reduce
from itertools import combinations
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, fv_ty, infer, restrict, subst_ty, v
from emit_agda import Emitter
from relative_coherence_based_columns import Brackets
from relative_coherence_cut import top_counts
from relative_coherence_hidden_seam import identity
from relative_coherence_simplex_sweeps import FlagSimplex, POINTS
from relative_coherence_tree_folds import weak_three_skeleton


def flip_routes(flag):
    top = flag.atom(flag.vertices)
    exterior = (0, 3, 5, 6)
    assert flag.atom(exterior)[:3] == top[:3]
    root = frozenset({exterior})
    routes = {root: ()}
    queue = deque([root])
    while queue:
        state = queue.popleft()
        for atom in combinations(flag.vertices, 5):
            source, target = map(frozenset, flag.atom(atom)[3])
            for before, after, sign in ((source, target, 1), (target, source, -1)):
                if before <= state and after.isdisjoint(state):
                    following = state - before | after
                    change = Counter(following)
                    change.subtract(state)
                    assert {s: n for s, n in change.items() if n} == {
                        s: sign * n for s, n in flag.d[atom].items()}
                    if following not in routes:
                        routes[following] = routes[state] + ((atom, sign),)
                        queue.append(following)
    fronts = {f for side in top[5] for a, _, b in flag.sweep(side, *top[4]) for f in (a, b)}
    slices = {frozenset(s) for f in fronts for s in flag.all_slices(f, top[3])}
    assert slices == routes.keys()
    return routes


def powered_column(ctx, tetrahedron):
    p = Brackets(0)
    p.ctx = ctx
    p.generators = {ty[2:]: v(i) for i, ty in enumerate(ctx) if ty != STAR}
    u = identity(ctx, tetrahedron)
    v_term = comp2(ctx, 3, u, u)
    five = p.bracket(u, v_term)
    # Both four-ends already loop at the exterior tetrahedron.
    based = comp2(p.ctx, 3, u, five)
    left, right = infer(p.ctx, based)[2:]
    assert top_counts(p.ctx, left) == top_counts(p.ctx, right)
    for power in (1, 2, 3, 5):
        def repeat(term):
            return reduce(lambda a, b: comp2(p.ctx, 3, a, b), [term] * power)

        lhs, rhs, witness = map(repeat, (left, right, based))
        assert infer(p.ctx, witness) == arr(infer(p.ctx, lhs), lhs, rhs)
        assert top_counts(p.ctx, witness) == {five[1]: power}
        alternative = p.bracket(lhs, rhs)
        six = p.bracket(alternative, witness)
        assert infer(p.ctx, six) == arr(infer(p.ctx, witness), alternative, witness)
        counts = top_counts(p.ctx, witness)
        counts.subtract(top_counts(p.ctx, alternative))
        assert dict(counts) == {five[1]: power, alternative[1]: -1}
    check_ctx(p.ctx)
    print('Powered replacement columns at 0356 checked for multiplicities 1, 2, 3 and 5.')


def local_inverses(flag, file):
    emitter = Emitter() if file else None
    ctx, atoms = weak_three_skeleton(flag)
    names = []
    for i, ty in enumerate(ctx):
        names.append({i} if ty == STAR else set().union(*(names[j] for j in fv_ty(ty))))
    exterior = (0, 3, 5, 6)
    keep = sorted(i for i, support in enumerate(names) if support <= set(exterior))
    small, _ = restrict(ctx, keep)
    powered_column(small, v(keep.index(atoms[exterior][1])))
    totals = Counter()
    for atom, term in atoms.items():
        rank = len(atom) - 1
        if not rank:
            continue
        p = Brackets(0)
        p.ctx = ctx
        p.generators = {ty[2:]: v(i) for i, ty in enumerate(ctx) if ty != STAR}
        ty = infer(ctx, term)
        source, target = ty[2:]
        reverse = p.bracket(target, source)
        reverse_type = arr(ty[1], target, source)
        assert infer(p.ctx, reverse) == reverse_type
        judgments = [(reverse, reverse_type)]
        for a, b, pole in ((term, reverse, source), (reverse, term, target)):
            product = comp2(p.ctx, rank - 1, a, b)
            unit = identity(p.ctx, pole)
            for start, end in ((product, unit), (unit, product)):
                law = p.bracket(start, end)
                law_type = arr(infer(p.ctx, start), start, end)
                assert infer(p.ctx, law) == law_type
                judgments.append((law, law_type))
            assert top_counts(p.ctx, product) == Counter([term[1], reverse[1]])
            assert not top_counts(p.ctx, unit)
        check_ctx(p.ctx)
        local = names.copy()
        for new in p.ctx[len(ctx):]:
            local.append(set().union(*(local[j] for j in fv_ty(new))))
            assert local[-1] <= set(atom)
        if emitter:
            keep = [i for i, support in enumerate(local) if support <= set(atom)]
            small, _ = restrict(p.ctx, keep)
            ren = tuple(v(keep.index(i)) if i in keep else None for i in range(len(local)))
            name = 'atom' + ''.join(map(str, atom))
            g = emitter.ctx(small)
            emitter.checks.extend([f'{name}-context : {g} ⊢ctx',
                                   f'{name}-context = from-just (checkCtx {g})'])
            for j, (w, expected) in enumerate(judgments):
                emitter.check_type(f'{name}-law{j}', small, ren[w[1]], subst_ty(expected, ren))
        totals[rank] += 1
    if emitter:
        file.write_text(emitter.module(file.stem, "Local simplex reverses and cancellation laws."))
    assert totals == {1: 21, 2: 35, 3: 35}
    print('91 reversed generating brackets and 364 ordered cancellation judgments checked.')


def verify(show, file):
    flag = FlagSimplex(POINTS)
    flag.check()
    paths = flip_routes(flag)
    rows = sorted((tuple(sorted(s)), path) for s, path in paths.items() if len(set().union(*s)) == 7)
    distances = [len(path) for _, path in rows]
    assert distances == [4, 5, 4, 3, 5, 4, 5, 4, 4, 3, 4, 3]
    print(f'{len(paths)} three-fronts reachable from 0356. Full-label distances:', *distances)
    if show:
        for i, (_, path) in enumerate(rows, 1):
            print(i, ' '.join(('+' if sign > 0 else '-') + ''.join(map(str, atom)) for atom, sign in path))
    local_inverses(flag, file)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--paths', action='store_true', help='print shortest signed routes to the twelve full labels')
    parser.add_argument('--agda', type=Path, help='emit all local inverse judgments')
    args = parser.parse_args()
    verify(args.paths, args.agda)
