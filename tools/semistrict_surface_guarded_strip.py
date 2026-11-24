"""Check the four-span degree-five split boundary and enumerate its positioned histories."""
from argparse import ArgumentParser
from pathlib import Path

from catt import comp2, disc_tree, fv_tm, fv_ty, infer, maximal_vars, src, tdim_tm, tgt, tree_ctx, v
from emit_agda import Emitter
from semistrict_surface_directed_power_queries import apply, chart, crossing, parallel_split, row_fit


def faces():
    rectangle = chart(1, 2)
    a, b, c = map(v, maximal_vars(rectangle))
    first = comp2(rectangle, 1, comp2(rectangle, 0, src(rectangle, a), b), crossing(rectangle, a, c))
    second = comp2(rectangle, 1, crossing(rectangle, a, b), comp2(rectangle, 0, tgt(rectangle, a), c))
    fit = row_fit(rectangle, tgt(rectangle, first), src(rectangle, second))
    first = comp2(rectangle, 2, first, fit)

    ctx = tree_ctx((disc_tree(1),) * 3 + (disc_tree(2),))
    a, b, c, g = map(v, maximal_vars(ctx))
    labels = (a, comp2(ctx, 0, b, src(ctx, c)), comp2(ctx, 0, tgt(ctx, b), c))
    f1, f2 = (apply(ctx, (rectangle, step), labels) for step in (first, second))
    left_end, right_start = tgt(ctx, tgt(ctx, f2)), src(ctx, src(ctx, g))
    changes = (comp2(ctx, 0, f1, right_start), comp2(ctx, 0, f2, right_start), comp2(ctx, 0, left_end, g))
    strip, direct, pasted = parallel_split(2, shift=1)
    return ctx, *(apply(ctx, (strip, term), changes) for term in (direct, pasted))


def histories():
    # The two names for the last slot are the signed 2-faces of its 3-globe.
    order = {letter: rank for rank, letter in enumerate('abcd')}
    order['D'] = order['d']
    paths = []

    def visit(word, steps):
        if word == 'abcD':
            paths.append(steps)
            return
        if 'd' in word:
            visit(word.replace('d', 'D'), steps + ('g',))
        for i, (left, right) in enumerate(zip(word, word[1:])):
            if order[left] > order[right]:
                visit(word[:i] + right + left + word[i + 2:], steps + (left + right,))

    visit('bcad', ())
    return paths


def exchange_graph(paths):
    # A bare inner exchange reverses adjacent blocks acting on ordered,
    # disjoint temporal intervals of the same 2-word. The d slot is last.
    sites = {'g': frozenset('d'), 'ca': frozenset('ca'), 'ba': frozenset('ba')}
    edges = set()
    for path in paths:
        for low in range(len(path)):
            for seam in range(low + 1, len(path)):
                for high in range(seam + 1, len(path) + 1):
                    right, left = path[low:seam], path[seam:high]
                    right_sites = frozenset.union(*(sites[step] for step in right))
                    left_sites = frozenset.union(*(sites[step] for step in left))
                    if right_sites.isdisjoint(left_sites) and right_sites == {'d'}:
                        target = path[:low] + left + right + path[high:]
                        assert target in paths
                        edges.add((path, target))
                        # A proper inner naturality would need a disjoint third event.
                        for outside in path[:low] + path[high:]:
                            assert sites[outside] & (right_sites | left_sites)
    return edges


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    ctx, direct, pasted = faces()
    assert direct != pasted and tdim_tm(ctx, direct) == 4
    boundary = infer(ctx, direct)
    assert infer(ctx, pasted) == boundary
    for face in (direct, pasted):
        assert set(fv_tm(face)) | set(fv_ty(boundary)) == set(range(len(ctx)))
    paths = histories()
    first, middle, last = ('g', 'ca', 'ba'), ('ca', 'g', 'ba'), ('ca', 'ba', 'g')
    assert sorted(paths) == sorted((first, middle, last))
    assert exchange_graph(paths) == {(first, middle), (middle, last), (first, last)}

    if args.agda_dir:
        emitter = Emitter()
        emitter.check_typed('direct', ctx, direct)
        emitter.check_type('pasted', ctx, pasted, boundary)
        emitter.checks.append(f'wide : cohCase {emitter.ctx(ctx)} {emitter.ty(boundary)} '
                              f'{emitter.tm(direct)} {emitter.tm(pasted)} ≡ false\nwide = refl\n')
        module = 'GuardedStrip'
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        source = emitter.module(module, __doc__)
        (args.agda_dir / (module + '.agda')).write_text(
            source.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))
    print('Both 4-faces are parallel and cover the tree. Three 3-histories, three block exchanges.')


if __name__ == '__main__':
    main()
