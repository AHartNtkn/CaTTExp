"""Transpose a full-support four-head into proper columns in the simplex star."""
from argparse import ArgumentParser
from functools import reduce
from pathlib import Path

from catt import (arr, check_ctx, comp2, fv_tm, fv_ty, infer, maximal_vars,
                  sub_from, subst_tm, subst_ty, tdim, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_based_columns import Brackets
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from relative_coherence_reduced_homology import BasedSkeleton


def join(ctx, cut, terms):
    return reduce(lambda a, b: comp2(ctx, cut, a, b), terms)


def grid(width):
    # Suspend twice a horizontal row of strings of two vertical two-cells.
    forest = tuple(((), ()) for _ in range(width))
    ctx = tree_ctx(((forest,),))
    slots = list(map(v, maximal_vars(ctx)))
    assert len(slots) == 2 * width
    pairs = list(zip(slots[::2], slots[1::2]))
    rows = comp2(ctx, 3, join(ctx, 2, slots[::2]), join(ctx, 2, slots[1::2]))
    columns = join(ctx, 2, (comp2(ctx, 3, a, b) for a, b in pairs))
    return ctx, rows, columns


def compress(chart, ty):
    """Replace each nonempty vertical string of four-discs by one four-disc."""
    ctx = []
    labels = []
    boundary_map = [None] * len(chart)
    i = 0
    while i < len(chart):
        if i + 1 < len(chart) and tdim(chart[i + 1]) == 3 and tdim(chart[i]) == 2:
            stop = i
            while (stop + 1 < len(chart) and tdim(chart[stop]) == 2
                   and tdim(chart[stop + 1]) == 3):
                stop += 2
            last = stop - 2
            # Only the last target and first source belong to the exterior.
            target = v(len(ctx))
            ctx.append(subst_ty(chart[last], boundary_map))
            boundary_map[last] = target
            source = subst_tm(chart[i + 1][2], boundary_map)
            ctx.append(arr(ctx[-1], source, target))
            labels.extend((v(last), join(chart, 3, (v(j) for j in range(i + 1, stop, 2)))))
            i = stop
        else:
            ctx.append(subst_ty(chart[i], boundary_map))
            boundary_map[i] = v(len(ctx) - 1)
            labels.append(v(i))
            i += 1
    ctx = tuple(ctx)
    check_ctx(ctx)
    local = head(ctx, *(subst_tm(t, boundary_map) for t in ty[2:]))
    folded = subst_tm(local, labels)
    assert infer(chart, folded) == ty
    return folded


def check(width, file):
    p = Brackets(width + 1)
    point = v(0)
    one = identity(p.ctx, point)
    two = identity(p.ctx, one)
    pure = identity(p.ctx, two)
    labels = []
    states = [pure]
    for i in range(1, width + 1):
        away, back = p.bracket(point, v(i)), p.bracket(v(i), point)
        detour = comp2(p.ctx, 0, away, back)
        for cut, start in [(1, one), (2, two)]:
            away, back = p.bracket(start, detour), p.bracket(detour, start)
            detour = comp2(p.ctx, cut, away, back)
        states.append(detour)
        labels.extend((p.bracket(pure, detour), p.bracket(detour, pure)))
    ctx = p.ctx
    check_ctx(ctx)
    chart, row, col = grid(width)
    sub = sub_from(chart, ctx, dict(zip(maximal_vars(chart), labels)))
    a, b = subst_tm(row, sub), subst_tm(col, sub)
    basis = BasedSkeleton(ctx)
    assert basis.counts(a) == {a: 1}
    local = [comp2(ctx, 3, x, y) for x, y in zip(labels[::2], labels[1::2])]
    assert basis.counts(b) == dict.fromkeys(local, 1)

    dependencies = []
    for i, ty in enumerate(ctx):
        names = {i} if i <= width else set()
        for j in fv_ty(ty):
            names.update(dependencies[j])
        dependencies.append(names)

    def colours(term):
        return set().union(*(dependencies[j] for j in fv_tm(term)))

    assert colours(a) == set(range(width + 1))
    assert [colours(t) for t in local] == [{0, i} for i in range(1, width + 1)]
    generic = head(chart, *infer(chart, row)[2:])
    folded = compress(chart, infer(chart, generic))
    c, d = (subst_tm(t, sub) for t in (generic, folded))
    assert basis.counts(c) == {c: 1} and basis.counts(d) == dict.fromkeys(local, 1)
    emitter = Emitter()
    for name, s, t, src, tgt in (('split', row, col, a, b), ('assemble', col, row, b, a),
                                  ('fold', generic, folded, c, d), ('unfold', folded, generic, d, c)):
        q = subst_tm(head(chart, s, t), sub)
        expected = arr(infer(ctx, src), src, tgt)
        assert infer(ctx, q) == expected
        assert basis.counts(q) == {q: 1}
        signed = basis.boundary(q)
        mixed = a if name in ('split', 'assemble') else c
        assert signed[mixed] == (-1 if name in ('split', 'fold') else 1)
        assert len(signed) == width + 1 and all(signed[x] == -signed[mixed] for x in local)
        if file:
            emitter.check_type(name, ctx, q, expected)
    # One string traversing all colours with adjacent two-colour segments.
    if width >= 3:
        states.append(pure)
        edges = [p.bracket(x, y) for x, y in zip(states, states[1:])]
        caps = [identity(p.ctx, pure)] + [p.bracket(x, pure) for x in states[1:-1]]
        word = edges[-1]
        forward = backward = identity(p.ctx, word)
        for i in reversed(range(len(edges) - 1)):
            short = comp2(p.ctx, 3, edges[i], caps[i+1])
            down, up = p.bracket(short, caps[i]), p.bracket(caps[i], short)
            forward = comp2(p.ctx, 4, comp2(p.ctx, 3, edges[i], forward), down)
            backward = comp2(p.ctx, 4, up, comp2(p.ctx, 3, edges[i], backward))
            word = comp2(p.ctx, 3, edges[i], word)
        check_ctx(p.ctx)
        for i in range(len(dependencies), len(p.ctx)):
            names = set().union(*(dependencies[j] for j in fv_ty(p.ctx[i])))
            assert len(names - {0}) <= 2
            dependencies.append(names)
        based = BasedSkeleton(p.ctx)
        assert based.counts(word) == {word: 1} and colours(word) == set(range(width + 1))
        for name, q, s, t, sign in (('cap', forward, word, caps[0], -1),
                                      ('uncap', backward, caps[0], word, 1)):
            expected = arr(infer(p.ctx, s), s, t)
            assert infer(p.ctx, q) == expected
            assert based.boundary(q) == {word: sign}
            if file:
                emitter.check_type(name, p.ctx, q, expected)
        print(f'Single string of {len(edges)} proper segments contracts to the identity in both directions.')
    if file:
        file.write_text(emitter.module(file.stem, 'Full-support column splitting in both directions.'))
    print(f'{width} vertical strings, {len(ctx)} declarations, '
          f'{width + 1} signed coordinates, one survives proper-row projection with coefficient ±1.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--width', type=int, default=6)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.width < 2:
        parser.error('use at least two strings to create a mixed-support head')
    check(args.width, args.agda)
