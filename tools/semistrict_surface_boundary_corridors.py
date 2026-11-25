"""Unfold a written query at its named lower positions and reachable versions."""
from argparse import ArgumentParser
from collections import defaultdict
from functools import cache
from itertools import product
from pathlib import Path

from catt import STAR, arr, comp2, infer, src, subst_tm, subst_ty, tdim, tgt, v
from semistrict_surface_inverse_completion import DerivationEmitter


def reachability(size, edges):
    reach = [{i} for i in range(size)]
    for a, b in edges:
        reach[a].add(b)
    for middle in range(size):
        for row in reach:
            if middle in row:
                row.update(reach[middle])
    return reach


def corridor(reach, first, last):
    return {i for i in reach[first] if last in reach[i]}


def check_graphs():
    # Compare the interval with independent walks: a vertex on a walk from
    # s to t can be visited by concatenating two simple paths of length < n.
    size = 3
    pairs = list(product(range(size), repeat=2))
    for mask in range(1 << len(pairs)):
        edges = [pair for i, pair in enumerate(pairs) if mask & (1 << i)]
        reach = reachability(size, edges)
        for start in range(size):
            walks = {(start, frozenset({start}))}
            visits = [set() for _ in range(size)]
            for _ in range(2 * size - 1):
                for end, seen in walks:
                    visits[end].update(seen)
                walks = {(b, seen | {b}) for end, seen in walks for a, b in edges if a == end}
            for end in range(size):
                allowed = corridor(reach, start, end)
                assert visits[end] == allowed
                for a, b in product(allowed, repeat=2):
                    assert corridor(reach, a, b) <= allowed


def raw_lifter(ctx, copies):
    @cache
    def lifts(term):
        if term[0] == 'v':
            return tuple(copies[term])
        _, arity, ty, labels = term
        prefixes = [()]
        for attachment, arg in zip(arity, labels, strict=True):
            options = lifts(arg)
            prefixes = [prefix + (choice,) for prefix in prefixes for choice in options
                        if infer(ctx, choice) == subst_ty(attachment, prefix)]
        return tuple(('coh', arity, ty, labels) for labels in prefixes)
    return lifts


def example(emitter, ordinary):
    old = ()

    def declare(ty):
        nonlocal old
        name = v(len(old))
        old += (ty,)
        return name

    x = declare(STAR)
    e = declare(arr(STAR, x, x))

    def arrow(s, t):
        assert infer(old, s) == infer(old, t)
        return declare(arr(infer(old, s), s, t))

    versions = [arrow(e, e) for _ in range(5)]
    a = versions[0]
    edges = [(0, 1), (1, 2), (2, 1), (1, 2), (0, 3), (3, 3), (4, 2)]
    moves = [arrow(versions[i], versions[j]) for i, j in edges]
    z, p, q, r, branch, cycle, _ = moves
    left, right = comp2(old, 2, z, p), comp2(old, 2, z, r)
    first, last = (p, r) if ordinary else (left, right)
    hold = arrow(first, first)
    change = arrow(first, last)
    upper = arrow(comp2(old, 3, hold, change), change)
    trapped_path = comp2(old, 2, branch, cycle)
    trapped = arrow(trapped_path, trapped_path)
    excluded = arrow(trapped, trapped)

    if ordinary:
        other = arrow(src(old, upper), tgt(old, upper))
        sixth = arrow(upper, other)
        high_names = (other, sixth)
    else:
        detour = comp2(old, 2, comp2(old, 2, z, p), q)
        detour = comp2(old, 2, detour, r)
        extra = arrow(detour, right)
        second = arrow(extra, extra)
        high_names = (extra, second)

    # The first column has two consecutive positions, both initially named a.
    # The second exterior column is a stationary copy of the original loop e.
    ctx = ()
    copies = defaultdict(list)
    fold = []

    def copy(name, ty):
        nonlocal ctx
        assert subst_ty(ty, tuple(fold)) == infer(old, name)
        new = v(len(ctx))
        ctx += (ty,)
        fold.append(name)
        copies[name].append(new)
        return new

    x0, x1, x2 = [copy(x, STAR) for _ in range(3)]
    wire = [copy(e, arr(STAR, x0, x1)) for _ in range(3)]
    spectator = copy(e, arr(STAR, x1, x2))
    reach = reachability(len(versions), edges)
    positions = []
    for slot, (start, end) in enumerate([(0, 0), (0, 2)]):
        allowed = corridor(reach, start, end)
        local = {i: copy(versions[i], arr(infer(ctx, wire[slot]), wire[slot], wire[slot + 1]))
                 for i in sorted(allowed)}
        positions.append(local)
        for name, (i, j) in zip(moves, edges, strict=True):
            if i in allowed and j in allowed:
                copy(name, arr(infer(ctx, local[i]), local[i], local[j]))

    for name in (hold, change, upper, trapped, excluded, *high_names):
        lift = raw_lifter(ctx, copies)
        for s, t in product(lift(src(old, name)), lift(tgt(old, name))):
            if infer(ctx, s) == infer(ctx, t):
                copy(name, arr(infer(ctx, s), s, t))
    assert not copies[trapped] and not copies[excluded]
    assert all(len(copies[name]) == 1 for name in (hold, change, upper, *high_names))
    if ordinary:
        for ty in ctx:
            if tdim(ty) + 1 == 4:
                assert ty[2][0] == ty[3][0] == 'v'
    assert len(copies[a]) == 2 and len(copies[e]) == 4
    lift = raw_lifter(ctx, copies)
    for tag, name in [('compound', upper), ('cycle', high_names[-1])]:
        change_old, change_new = name, copies[name][0]
        if ordinary:
            tag += 'WithGlobularFour'
            change_old = comp2(old, 2, z, change_old)
            change_new = comp2(ctx, 2, copies[z][0], change_new)
        old_query = comp2(old, 0, comp2(old, 1, a, change_old), e)
        actual = comp2(ctx, 0, comp2(ctx, 1, positions[0][0], change_new), spectator)
        assert lift(old_query) == (actual,)
        assert lift(src(old, old_query)) == (src(ctx, actual),)
        assert lift(tgt(old, old_query)) == (tgt(ctx, actual),)
        assert subst_tm(actual, tuple(fold)) == old_query
        if emitter:
            emitter.check_type(tag + 'AtPositions', ctx, actual, infer(ctx, actual))
            emitter.check_type(tag + 'Folded', old, subst_tm(actual, tuple(fold)), infer(old, old_query))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    check_graphs()
    emitter = DerivationEmitter() if args.agda_dir else None
    example(emitter, ordinary=False)
    example(emitter, ordinary=True)
    if emitter:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('BoundaryCorridors', __doc__).replace(
            'open import CaTTExp.Pure\n', 'open import CaTTExp.Gray.Pure\n'
            'open import CaTTExp.Pure using (∅)\n'
            'open import CaTTExp.PastingCheck ∅ using () renaming (checkPs to pastable)\n')
        (args.agda_dir / 'BoundaryCorridors.agda').write_text(module)
    print('Checked directed intervals on 512 graphs and unique raw lifts of three 5-cells and one 6-cell.')


if __name__ == '__main__':
    main()
