"""Check singleton top cuts and literal whiskered junctions in CaTT."""

import argparse
from collections import Counter
from pathlib import Path

from catt import (arr, comp2, comp_tree, disc_tree, infer, maximal_vars, src,
                  sub_from, subst_tm, tdim_tm, tgt, tree_ctx, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_full_support_cuts import pole, support
from gray_globe_comparison import atom, strict_cells
from gray_globe_exterior_actions import certificate, coherence
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import string_tree


def strict_junctions(shape, rank):
    cells = strict_cells(shape, rank)
    singletons = {c for c in cells if len(c[-1][0]) == 1}
    padded = sum(c != atom(c[-1][0][0]) for c in singletons)
    # Enumerate all temporal pairs over a single top occurrence, including units.
    by_source = {}
    for cell in cells:
        by_source.setdefault(pole(cell, rank-1, 0), []).append(cell)
    pairs = 0
    for left in cells:
        for right in by_source[pole(left, rank-1, 1)]:
            if len(left[-1][0]) + len(right[-1][0]) != 1:
                continue
            full, unit = (left, right) if left[-1][0] else (right, left)
            assert full in singletons and support(unit) < support(full)
            assert pole(unit, rank-1, 0) == pole(unit, rank-1, 1)
            pairs += 1
    assert pairs == 2 * len(singletons)
    print(f"{shape}, rank {rank}: {len(singletons)} singletons, {padded} with padding, {pairs} unit cuts")


def act(ctx, rank, term, stage):
    if stage == 0:
        return term
    degree = tdim_tm(ctx, term)
    face = term if degree == rank else src(ctx, term)
    left, right = (ident(ctx, p) for p in (src(ctx, face), tgt(ctx, face)))
    if stage % 2:
        left = comp2(ctx, rank-1, left, left)
    else:
        right = comp2(ctx, rank-1, right, right)
    return comp_tree(string_tree(rank-1, [rank, degree, rank]), ctx, [left, term, right])


def lifted_chain(rank, stages):
    ctx = tree_ctx(string_tree(rank, [rank+1] * stages))
    events = [v(i) for i in maximal_vars(ctx)]
    disk = tree_ctx(disc_tree(rank))
    (top,) = maximal_vars(disk)
    result = events[0]
    for stage, event in enumerate(events[1:], 1):
        before = act(disk, rank, v(top), stage-1)
        after = act(disk, rank, v(top), stage)
        change = coherence(disk, before, after)
        sigma = sub_from(disk, ctx, {top: src(ctx, event)})
        bridge = subst_tm(change, sigma)
        whiskered = act(ctx, rank, event, stage)
        assert tgt(ctx, result) == src(ctx, bridge)
        assert tgt(ctx, bridge) == src(ctx, whiskered)
        result = comp2(ctx, rank, comp2(ctx, rank, result, bridge), whiskered)
    wanted = arr(infer(ctx, src(ctx, events[0])), src(ctx, events[0]),
                 act(ctx, rank, tgt(ctx, events[-1]), stages-1))
    assert infer(ctx, result) == wanted
    assert top_counts(ctx, result) == Counter(maximal_vars(ctx))
    return ctx, result, wanted


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path)
    args = parser.parse_args()
    for shape in ((4, 4), (2, 2, 2), (1, 1, 1, 1, 1)):
        strict_junctions(shape, 4)
    for rank in (2, 3, 4, 5):
        ctx, result, wanted = lifted_chain(rank, 3)
        if rank == 4 and args.agda:
            emitter = Emitter()
            certificate(emitter, ctx)("whiskered-junctions", result, wanted)
            args.agda.write_text(emitter.module(args.agda.stem, "Two pole adjustments along a chain."))
    print("Literal ends and top occurrences checked on three-event chains in ranks 3–6.")
