"""Check directed old five-boundaries across independent high base attachments."""

from argparse import ArgumentParser
from collections import deque
from itertools import permutations
from pathlib import Path

from catt import arr, check_ctx, comp2, fv_tm, infer, subst_tm, subst_ty, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from relative_coherence_middle_wire import check_context


def high_cells(base):
    # Two rank-five writings at the same four-cell, using only the base.
    track = identity(base, v(13))
    unit = identity(base, track)
    twice = comp2(base, 4, unit, unit)
    ctx = base
    for start, end in ((unit, twice), (twice, unit)):
        ctx += (arr(infer(ctx, start), start, end),)
    round_trip = comp2(ctx, 5, v(len(base)), v(len(base) + 1))
    finish = identity(ctx, unit)
    assert infer(ctx, round_trip) == infer(ctx, finish)
    return ctx + (arr(infer(ctx, finish), round_trip, finish),)


def attach(ctx, edges, pole):
    four_type = arr(infer(ctx, pole), pole, pole)
    points = [v(len(ctx) + i) for i in range(3)]
    ctx += (four_type,) * len(points)
    arrows = {}
    for i, j in edges:
        arrows[i, j] = v(len(ctx))
        ctx += (arr(four_type, points[i], points[j]),)
    check_ctx(ctx)
    return ctx, points, arrows


def paths_from(source, arrows):
    paths = {source: ()}
    queue = deque([source])
    while queue:
        i = queue.popleft()
        for edge in arrows:
            start, end = edge
            if start == i and end not in paths:
                paths[end] = paths[i] + (edge,)
                queue.append(end)
    return paths


def check():
    base = check_context()
    high = high_cells(base)
    check_ctx(high)
    count_high = len(high) - len(base)
    options = tuple(permutations(range(3), 2))
    inhabited = excluded = 0
    emitter = Emitter()
    for bits in range(1 << len(options)):
        edges = [edge for k, edge in enumerate(options) if bits & (1 << k)]
        old, points, arrows = attach(base, edges, v(13))
        new, new_points, _ = attach(high, edges, v(13))
        rename = [v(i if i < len(base) else i + count_high) for i in range(len(old))]
        assert all(subst_ty(ty, rename) == infer(new, image) for ty, image in zip(old, rename))
        for i in range(3):
            paths = paths_from(i, arrows)
            for j in range(3):
                if j not in paths:
                    # Indicator of the reachable cut is nondecreasing on every
                    # strict generating 5-column, including in the extended context.
                    assert i in paths and all(a not in paths or b in paths for a, b in edges)
                    excluded += 1
                    continue
                path = paths[j]
                if path:
                    witness = arrows[path[0]]
                    for edge in path[1:]:
                        witness = comp2(old, 4, witness, arrows[edge])
                else:
                    witness = identity(old, points[i])
                lifted = subst_tm(witness, rename)
                expected = arr(infer(new, new_points[i]), new_points[i], new_points[j])
                assert infer(old, witness) == arr(infer(old, points[i]), points[i], points[j])
                assert infer(new, lifted) == expected
                assert not fv_tm(lifted).intersection(range(len(base), len(high)))
                inhabited += 1
                if edges == [(0, 1), (1, 2)] and (i, j) == (0, 2):
                    emitter.check_type('oldPath', old, witness, infer(old, witness))
                    emitter.check_type('transportedPath', new, lifted, expected)
                    emitter.check_eq('transport', witness, rename, lifted)
                    g = emitter.ctx(new)
                    emitter.checks.append(f'extended : {g} ⊢ctx\nextended = from-just (checkCtx {g})\n')
    print(f'64 directed graphs: {inhabited} typed old paths, {excluded} unreachable cuts before and after high completion samples')
    return emitter


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = check()
    if args.agda_dir:
        name = 'HighBaseCompletion'
        (args.agda_dir / (name + '.agda')).write_text(emitter.module(name, __doc__))
