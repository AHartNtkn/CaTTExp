"""Check based interchanges at a free generator and strict markings of 2-grids."""

import argparse
from itertools import product
from pathlib import Path

from catt import (STAR, arr, chain_tree, check_ctx, coh_between, comp2, disc_tree, infer,
                  maximal_vars, src, sub_from, subst_tm, tgt, tree_ctx, v)
from ct_suspension import susp_ctx
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity


def check_interchanges(emitter):
    graph = (STAR, arr(STAR, v(0), v(0)))
    doubled = comp2(graph, 0, v(1), v(1))
    repeated_faces = graph + (arr(graph[1], doubled, doubled),)
    for rank in range(1, 5):
        ctx = graph if rank == 1 else repeated_faces
        if rank >= 2:
            repeated_faces = susp_ctx(repeated_faces)
        g = v(len(ctx) - 1)
        extended = ctx + (arr(infer(ctx, g), g, g),)
        check_ctx(extended)
        loop = v(len(ctx))
        tree = disc_tree(rank)
        disk = tree_ctx(tree)
        z = v(len(disk) - 1)
        padded = comp2(disk, rank - 1, z, identity(disk, tgt(disk, z)))
        out = coh_between(disk, tree, [z], z, padded)
        back = coh_between(disk, tree, [z], padded, z)
        h = comp2(disk, rank, out, back)
        upper_tree = disc_tree(rank + 1)
        upper = tree_ctx(upper_tree)
        crossing = v(len(upper) - 1)

        def specialize(term, target, at):
            return subst_tm(term, sub_from(disk, target, {z[1]: at}))

        left = comp2(upper, rank, specialize(h, upper, src(upper, crossing)), crossing)
        right = comp2(upper, rank, crossing, specialize(h, upper, tgt(upper, crossing)))
        interchange = coh_between(upper, upper_tree, [crossing], left, right)
        h_g = specialize(h, extended, g)
        doubled_loop = comp2(extended, rank, h_g, h_g)
        for suffix, k in [('variable', loop), ('structural', doubled_loop)]:
            s = sub_from(upper, extended, {crossing[1]: k})
            witness = subst_tm(interchange, s)
            hk, kh = comp2(extended, rank, h_g, k), comp2(extended, rank, k, h_g)
            expected = arr(infer(extended, hk), hk, kh)
            assert hk != kh and infer(extended, witness) == expected
            label = f'interchange-{rank}-{suffix}'
            emitter.check_typed(label, extended, witness)
            emitter.check_type(label, extended, witness, expected)


def check_repeated_paths(emitter):
    for rank in (2, 3):
        disk = tree_ctx(disc_tree(rank))
        base = disk[:-1]
        source, target = disk[-1][2:]
        tree = disc_tree(rank - 1)
        pole_disk = tree_ctx(tree)
        pole = v(len(pole_disk) - 1)
        padded = comp2(pole_disk, rank - 2, pole, identity(pole_disk, tgt(pole_disk, pole)))
        unitor = coh_between(base, tree, [source], pole, padded)

        def model(padding, endpoints):
            ctx = base
            writes, edges = [], []
            for pad in padding:
                a = tgt(base, unitor) if pad else source
                vertex = v(len(ctx))
                ctx += (arr(infer(base, source), a, target),)
                writes.append(comp2(ctx, rank - 1, unitor, vertex) if pad else vertex)
            for i, j in endpoints:
                edges.append(v(len(ctx)))
                ctx += (arr(infer(ctx, writes[i]), writes[i], writes[j]),)
            check_ctx(ctx)
            return ctx, edges

        graph, edges = model((False, True), [(0, 1), (1, 0)])
        interval, occurrences = model((False, True, False, True), [(0, 1), (1, 2), (2, 3)])
        vertices = [v(len(base) + i) for i in (0, 1, 0, 1)]
        word = [edges[0], edges[1], edges[0]]
        projection = tuple(v(i) for i in range(len(base))) + tuple(vertices + word)
        # The three input edges form a path at the m-cut. The middle vertex
        # carries a whiskered source in both presentations.
        path = chain_tree(3)
        for _ in range(rank):
            path = (path,)
        arity = tree_ctx(path)
        a, b, c = (v(i) for i in maximal_vars(arity))
        left = comp2(arity, rank, comp2(arity, rank, a, b), c)
        right = comp2(arity, rank, a, comp2(arity, rank, b, c))
        upstairs = coh_between(interval, path, occurrences, left, right)
        downstairs = coh_between(graph, path, word, left, right)
        assert subst_tm(upstairs, projection) == downstairs
        assert infer(graph, downstairs)[2] != infer(graph, downstairs)[3]
        for name, ctx, cell in [('interval', interval, upstairs), ('cycle', graph, downstairs)]:
            emitter.check_typed(f'{name}-{rank}', ctx, cell)
        emitter.check_eq(f'fold-{rank}', upstairs, projection, downstairs)


def compositions(total, length):
    if length == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in compositions(total - first, length - 1):
                yield (first,) + rest


def check_grids():
    # The two parallel arrows L,R of D² both project to ff, the top to g^power.
    # Enumerate its possible rectangular labellings by the horizontal object cut
    # and all vertical histories in the column crossing that cut.
    tested = 0
    for cols, rows, power in product(range(1, 5), range(1, 5), (1, 2)):
        lifts = {}
        for col in range(cols):
            widths = tuple(2 * (i == col) for i in range(cols))
            for middle in product('LR', repeat=rows - 1):
                history = ('L',) + middle + ('R',)
                transitions = list(zip(history, history[1:]))
                if ('R', 'L') in transitions:
                    continue
                cells = tuple(power * (i == col and step == ('L', 'R'))
                              for i in range(cols) for step in transitions)
                key = (widths, cells)
                lifts[key] = lifts.get(key, 0) + 1
        for widths in compositions(2, cols):
            # Each g needs the entire two-letter word at its position.
            for cells in compositions(power, cols * rows):
                if any(n and widths[j // rows] < 2 for j, n in enumerate(cells)):
                    continue
                assert lifts.get((widths, cells), 0) == int(power in cells)
                tested += 1
    return tested


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    check_interchanges(emitter)
    check_repeated_paths(emitter)
    count = check_grids()
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Based loop interchanges.'))
    print(f'8 based interchanges in ranks 1–4 and {count} marked grids checked; 2 repeated-edge folds checked')
