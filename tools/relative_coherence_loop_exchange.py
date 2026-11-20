"""Build a raw CaTT exchange between arbitrary two-endomorphisms of an identity."""
from argparse import ArgumentParser
from collections import Counter
from functools import reduce
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, tgt, tree_ctx, v)
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_hom_chains import boundary, hom_chain


def instance(ctx, chart, term, labels):
    return subst_tm(term, sub_from(chart, ctx, dict(zip(maximal_vars(chart), labels, strict=True))))


def paste(ctx, cut, steps):
    return reduce(lambda a, b: comp2(ctx, cut, a, b), steps)


def path(ctx, start, edges):
    return paste(ctx, 1, edges) if edges else ident(ctx, start)


def grouped(ctx, start, edges, pre, mid):
    middle_start = tgt(ctx, edges[pre-1]) if pre else start
    groups = ([path(ctx, start, edges[:pre])] if pre else [])
    groups.append(path(ctx, middle_start, edges[pre:pre+mid]))
    if edges[pre+mid:]:
        groups.append(paste(ctx, 1, edges[pre+mid:]))
    return paste(ctx, 1, groups)


def regroup(ctx, start, edges, pre, mid, reverse):
    chart = tree_ctx(string_tree(1, [2]*len(edges)))
    generic = list(map(v, maximal_vars(chart))) if edges else []
    base = src(chart, generic[0]) if generic else v(len(chart)-1)
    a = path(chart, base, generic)
    b = grouped(chart, base, generic, pre, mid)
    term = head(chart, b, a) if reverse else head(chart, a, b)
    return instance(ctx, chart, term, edges or [start])


def replace(ctx, start, word, offset, old, new, change):
    """Whisker a local relation with the surrounding path, including empty blocks."""
    assert word[offset:offset+len(old)] == old
    prefix, suffix = word[:offset], word[offset+len(old):]
    base = tgt(ctx, prefix[-1]) if prefix else start
    assert infer(ctx, change)[2:] == (path(ctx, base, old), path(ctx, base, new))
    result = prefix + new + suffix
    tracks = [regroup(ctx, start, word, len(prefix), len(old), False)]
    if prefix:
        change = comp2(ctx, 1, paste(ctx, 1, prefix), change)
    if suffix:
        change = comp2(ctx, 1, change, paste(ctx, 1, suffix))
    tracks += [change, regroup(ctx, start, result, len(prefix), len(new), True)]
    return result, paste(ctx, 2, tracks)


def unit(ctx, arrow, left):
    chart = tree_ctx(disc_tree(1))
    f = v(2)
    extended = (comp2(chart, 0, ident(chart, v(0)), f) if left
                else comp2(chart, 0, f, ident(chart, v(1))))
    return instance(ctx, chart, head(chart, extended, f), [arrow])


def slide(ctx, cell, left, reverse):
    chart = tree_ctx(disc_tree(2))
    a = v(4)
    extended = (comp2(chart, 0, ident(chart, v(0)), a) if left
                else comp2(chart, 0, a, ident(chart, v(1))))
    plain = comp2(chart, 1, unit(chart, src(chart, a), left), a)
    moved = comp2(chart, 1, extended, unit(chart, tgt(chart, a), left))
    square = head(chart, moved, plain) if reverse else head(chart, plain, moved)
    return instance(ctx, chart, square, [cell])


def exchange(ctx, point, a, b):
    base = ident(ctx, point)
    for cell in [a, b]:
        assert infer(ctx, cell) == arr(infer(ctx, base), base, base)
    chart = tree_ctx(())
    i = ident(chart, v(0))
    right, left = unit(chart, i, False), unit(chart, i, True)
    inverse = head(chart, i, src(chart, right))
    ins = head(chart, ident(chart, i), comp2(chart, 1, inverse, right))
    rem = head(chart, comp2(chart, 1, inverse, right), ident(chart, i))
    rl, lr = head(chart, right, left), head(chart, left, right)
    right, left, inverse, ins, rem, rl, lr = [
        instance(ctx, chart, t, [point]) for t in (right, left, inverse, ins, rem, rl, lr)]
    ar, bl = comp2(ctx, 0, a, base), comp2(ctx, 0, base, b)
    chart = tree_ctx(string_tree(0, [2, 2]))
    u, w = map(v, maximal_vars(chart))
    first = comp2(chart, 1, comp2(chart, 0, u, src(chart, w)), comp2(chart, 0, tgt(chart, u), w))
    last = comp2(chart, 1, comp2(chart, 0, src(chart, u), w), comp2(chart, 0, u, tgt(chart, w)))
    crossing = instance(ctx, chart, head(chart, first, last), [a, b])
    word, tracks = [a, b], []
    for pos, old, new, proof in [
        (0, [], [inverse, right], ins),
        (1, [right, a], [ar, right], slide(ctx, a, False, False)),
        (2, [right], [left], rl),
        (2, [left, b], [bl, left], slide(ctx, b, True, False)),
        (1, [ar, bl], [bl, ar], crossing),
        (3, [left], [right], lr),
        (2, [ar, right], [right, a], slide(ctx, a, False, True)),
        (2, [right], [left], rl),
        (1, [bl, left], [left, b], slide(ctx, b, True, True)),
        (1, [left], [right], lr),
        (0, [inverse, right], [], rem),
    ]:
        word, track = replace(ctx, base, word, pos, old, new, proof)
        tracks.append(track)
    assert word == [b, a]
    return paste(ctx, 2, tracks)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    point = v(0)
    i = ident((STAR,), point)
    loop = arr(arr(STAR, point, point), i, i)
    ctx = (STAR, loop, loop)
    a, b = v(1), v(2)
    start, end = comp2(ctx, 1, a, b), comp2(ctx, 1, b, a)
    ty = arr(infer(ctx, start), start, end)
    result = exchange(ctx, point, a, b)
    assert infer(ctx, result) == ty and start != end
    # Two columns can cancel an intermediate edge which neither input uses.
    point_ctx = (STAR,)
    right, left = unit(point_ctx, i, False), unit(point_ctx, i, True)
    inverse = head(point_ctx, i, src(point_ctx, right))
    p = head(point_ctx, i, i)
    q = comp2(point_ctx, 1, inverse, right)
    r = comp2(point_ctx, 1, inverse, left)
    pp = comp2(point_ctx, 1, p, p)
    pr, rp = comp2(point_ctx, 1, p, r), comp2(point_ctx, 1, r, p)
    positive, negative = head(point_ctx, pp, q), head(point_ctx, pr, q)
    return_track = head(point_ctx, q, pr)
    signed = paste(point_ctx, 2, [positive, return_track, exchange(point_ctx, point, p, r)])
    signed_type = arr(infer(point_ctx, pp), pp, rp)
    assert infer(point_ctx, signed) == signed_type
    difference = hom_chain(point_ctx, rp).copy()
    difference.subtract(hom_chain(point_ctx, pp))
    columns = Counter(boundary(point_ctx, positive))
    columns.subtract(boundary(point_ctx, negative))
    assert columns == difference and any(difference.values())
    print('Checked universal loop exchange and a signed two-column comparison above the point.')
    if args.agda:
        emitter = Emitter()
        emitter.check_type('swap', ctx, result, ty)
        emitter.check_type('signed', point_ctx, signed, signed_type)
        args.agda.write_text(emitter.module(args.agda.stem, 'Loop exchange and a signed comparison above the point.'))


if __name__ == '__main__':
    main()
