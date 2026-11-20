"""Check the endpoint folds for top generators subdivided into four links."""

from argparse import ArgumentParser
from itertools import combinations, product
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, fv_tm, infer, src, sub_from, subst_tm,
                  subst_ty, tgt, v)
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_globe_padding import disk
from relative_coherence_hidden_seam import identity


def prune(block):
    """Return (link, free end) for one component of a union of short paths."""
    for event, j in sorted(block):
        if j < 3 and (event, j + 1) not in block:
            return (event, j), 'target'
        if j > 0 and (event, j - 1) not in block:
            return (event, j), 'source'
    raise ValueError('every remaining component connects both old ends')


def fold_cert(rank, free):
    ctx, z = disk(rank)
    a, b = src(ctx, z), tgt(ctx, z)
    u = z
    w = ('coh', ctx, infer(ctx, z), tuple(map(v, range(len(ctx)))))
    h = head(ctx, u, w)
    hh = comp2(ctx, rank, h, identity(ctx, w))
    assert h != hh and u != w

    # Construct the post-fold comparison on the smaller disk.
    lower, shared = disk(rank - 1)
    fold = sub_from(ctx, lower, {z[1]: identity(lower, shared)})
    low = head(lower, subst_tm(h, fold), subst_tm(hh, fold))
    endpoint = a if free == 'target' else b
    inclusion = sub_from(lower, ctx, {shared[1]: endpoint})
    low = subst_tm(low, inclusion)
    folded = sub_from(ctx, ctx, {z[1]: identity(ctx, endpoint)})
    horizontal = lambda p, q: comp2(ctx, rank - 1, p, q)
    temporal = lambda p, q: comp2(ctx, rank, p, q)
    paste = lambda p, q: comp2(ctx, rank + 1, p, q)
    if free == 'target':
        whisker = lambda t: horizontal(t, z)
        ku, kw = (head(ctx, whisker(subst_tm(t, folded)), t) for t in (u, w))
        insert = lambda t: temporal(ku, t)
        other = lambda t: temporal(whisker(t), kw)
        move_back = head(ctx, tgt(ctx, ku), src(ctx, ku))
        undo = lambda t: temporal(move_back, t)
    else:
        whisker = lambda t: horizontal(z, t)
        ku, kw = (head(ctx, t, whisker(subst_tm(t, folded))) for t in (u, w))
        insert = lambda t: temporal(t, kw)
        other = lambda t: temporal(ku, whisker(t))
        move_back = head(ctx, tgt(ctx, kw), src(ctx, kw))
        undo = lambda t: temporal(t, move_back)

    # These two oriented prisms are the specialization of N in the proof.
    # All their data here are generic on a single disk.
    before = head(ctx, insert(h), other(subst_tm(h, folded)))
    after = head(ctx, other(subst_tm(hh, folded)), insert(hh))
    transported = paste(paste(before, other(low)), after)
    result = paste(paste(head(ctx, h, undo(insert(h))), undo(transported)),
                   head(ctx, undo(insert(hh)), hh))
    assert infer(ctx, result) == arr(infer(ctx, h), h, hh)
    return ctx, z, h, hh, result


def board(lower, pairs, blocks, knots):
    # Each square has two composite old ends. Its three fresh knots
    # are independent of the second square's knots.
    ctx = lower
    names = {}
    for knot in sorted(knots):
        names[knot] = v(len(ctx))
        ctx += (infer(lower, pairs[knot[0]][0]),)
    ends = {}
    for event, edge in sorted(blocks):
        a, b = pairs[event]
        start = a if edge == 0 else names[event, edge]
        end = b if edge == 3 else names[event, edge + 1]
        ends[event, edge] = start, end
        names[event, 'edge', edge] = v(len(ctx))
        ctx += (arr(infer(ctx, start), start, end),)
    check_ctx(ctx)
    return ctx, names, ends


def verify(rank, lower, pairs, emitter):
    universe = list(product(range(2), range(4)))
    samples = {}
    counts = [0, 0]
    for k in range(4):
        for selected in combinations(universe, k):
            block = set(selected)
            knots = {(e, i) for e, j in block for i in (j, j + 1) if 0 < i < 4}
            while block:
                ctx, names, ends = board(lower, pairs, block, knots)
                (event, j), free = prune(block)
                target_free = free == 'target'
                knot = event, j + int(target_free)
                link = names[event, 'edge', j]
                kept_end = ends[event, j][int(not target_free)]
                next_block, next_knots = block - {(event, j)}, knots - {knot}
                dst, retained, _ = board(lower, pairs, next_block, next_knots)
                fold = {v(i): v(i) for i in range(len(lower))}
                fold.update({names[key]: retained[key] for key in retained})
                values = {old[1]: new for old, new in fold.items()}
                at = subst_tm(kept_end, values)
                values[names[knot][1]] = at
                values[link[1]] = identity(dst, at)
                sigma = tuple(values[i] for i in range(len(ctx)))
                assert all(infer(dst, t) == subst_ty(ty, sigma) for t, ty in zip(sigma, ctx))
                if free not in samples and kept_end[0] == 'coh':
                    samples[free] = (ctx, link, dst, sigma)
                counts[0 if target_free else 1] += 1
                block, knots = next_block, next_knots
    assert len(samples) == 2
    for free, (ctx, link, dst, sigma) in samples.items():
        generic, z, h, hh, result = fold_cert(rank, free)
        assignment = sub_from(generic, ctx, {z[1]: link})
        start, end, term = (subst_tm(t, assignment) for t in (h, hh, result))
        expected = arr(infer(ctx, start), start, end)
        assert start != end and infer(ctx, term) == expected
        assert link[1] in fv_tm(term)
        assert infer(dst, subst_tm(term, sigma)) == subst_ty(expected, sigma)
        if rank == 2:
            emitter.check_type('prune-' + free, ctx, term, expected)
    return counts


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    # Horizontally adjacent squares. Their events can occur in either order.
    lower = (STAR,) * 7
    pairs = []
    for start in (0, 3):
        paths = []
        for middle in (start + 1, start + 2):
            first = len(lower)
            lower += (arr(STAR, v(start), v(middle)), arr(STAR, v(middle), v(start + 3)))
            paths.append(comp2(lower, 0, v(first), v(first + 1)))
        pairs.append(paths)
    emitter = Emitter()
    for rank in range(2, 5):
        l, r = verify(rank, lower, pairs, emitter)
        print(f'Rank {rank}: 93 blocks, {l} target folds and {r} source folds; both tracks checked.')
        lower = susp_ctx(lower)
        pairs = [(susp_tm(a), susp_tm(b)) for a, b in pairs]
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Folded four-link comparisons at composite ends.'))
