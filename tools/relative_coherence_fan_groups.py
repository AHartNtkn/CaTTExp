"""Check walking fan contractions and both five-cell comparisons of fourth inverses."""
from argparse import ArgumentParser
from collections import Counter
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, fv_tm, fv_ty, infer, maximal_vars,
                  restrict, src, sub_from, subst_tm, subst_ty, tdim, tgt, tree_ctx, v)
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import composite, head, string_tree
from relative_coherence_walking_graph import instantiate, linear, signed, template


def compare_inverses(ctx, work, sigma, emitter):
    # Two inverse generators and the two temporal cancellation five-cells.
    pairs = [(sigma[b], sigma[p]) for b, p in work.inverse_pairs if tdim(work.ctx[b]) == 3]
    (b, cancel_fb), (c, cancel_cf) = pairs[:2]
    fb, cf = src(ctx, cancel_fb), src(ctx, cancel_cf)
    f = fb[3][maximal_vars(fb[1])[0]]
    assert comp2(ctx, 3, f, b) == fb
    assert comp2(ctx, 3, c, f) == cf

    def reverse_var(cell):
        ty = arr(infer(ctx, src(ctx, cell)), tgt(ctx, cell), src(ctx, cell))
        return next(u for u in sigma[work.forward:] if infer(ctx, u) == ty)
    expand_fb, expand_cf = map(reverse_var, (cancel_fb, cancel_cf))

    disk = tree_ctx(disc_tree(4))
    slot = v(len(disk)-1)
    chart = tree_ctx(string_tree(3, (4,4,4)))
    x, y, z = map(v, maximal_vars(chart))
    left, right = comp2(chart, 3, comp2(chart, 3, x, y), z), comp2(chart, 3, x, comp2(chart, 3, y, z))
    def generic(model, a, d, labels):
        sub = sub_from(model, ctx, dict(zip(maximal_vars(model), labels, strict=True)))
        return tuple(subst_tm(head(model, l, r), sub) for l, r in ((a,d),(d,a)))
    enter, leave = generic(disk, slot, comp2(disk, 3, ident(disk, src(disk, slot)), slot), [b])
    assoc, unassoc = generic(chart, left, right, [c,f,b])
    finish, start = generic(disk, comp2(disk, 3, slot, ident(disk, tgt(disk, slot))), slot, [c])
    forward = composite(ctx, 4, [enter, comp2(ctx, 3, expand_cf, b), assoc,
                                 comp2(ctx, 3, c, cancel_fb), finish])
    backward = composite(ctx, 4, [start, comp2(ctx, 3, c, expand_fb), unassoc,
                                  comp2(ctx, 3, cancel_cf, b), leave])
    pad = ident(ctx, tgt(ctx, b))
    for power in range(6):
        if power in (0, 1, 5):
            for name, value, a, d in [('forward',forward,b,c), ('backward',backward,c,b)]:
                term = comp2(ctx, 3, value, pad)
                start_term, end_term = comp2(ctx, 3, a, pad), comp2(ctx, 3, d, pad)
                ty = arr(infer(ctx, start_term), start_term, end_term)
                assert infer(ctx, term) == ty
                if emitter and power == 1:
                    support = set(fv_tm(term) | fv_ty(ty))
                    for i in sorted(range(len(ctx)), reverse=True):
                        if i in support:
                            support.update(fv_ty(ctx[i]))
                    small, inclusion = restrict(ctx, support)
                    ren = [None]*len(ctx)
                    for i, u in enumerate(inclusion):
                        ren[u[1]] = v(i)
                    reduced, wanted = subst_tm(term, ren), subst_ty(ty, ren)
                    assert subst_tm(reduced, inclusion) == term and subst_ty(wanted, inclusion) == ty
                    emitter.check_type(name, small, reduced, wanted)
        pad = comp2(ctx, 3, pad, fb)


def fan(n, height, certify, emitter=None):
    ctx = (STAR,)
    h = [Counter()]
    def attach(k, old):
        nonlocal ctx
        work = template(k, height)
        added, sigma = instantiate(ctx, work, old)
        ctx += added
        h.extend(Counter() for _ in added)
        g, a = sigma[work.duplicate], sigma[work.forward]
        h[g[1]] = linear(h, top_counts(ctx, old))
        h[g[1]][a[1]] += 1
        for inv, cancel in work.inverse_pairs:
            h[sigma[inv][1]] = Counter({sigma[cancel][1]: -1})
        return work, sigma

    rays = []
    for _ in range(n):
        work, sigma = attach(0, v(0))
        rays.append((sigma[work.forward], sigma[work.forward+1]))
    for j in range(n-1):
        anchor = comp2(ctx, 0, rays[j][1], rays[j+1][0])
        for slot in range(n):
            work, sigma = attach(1, anchor)
            if certify and j == slot == 0:
                compare_inverses(ctx, work, sigma, emitter)
    boundary = [Counter() if ty == STAR else signed(top_counts(ctx, ty[3]), top_counts(ctx, ty[2]))
                for ty in ctx]
    entries = 0
    for i, ty in enumerate(ctx):
        if tdim(ty)+1 >= height:
            continue
        dh, hd = linear(boundary, h[i]), linear(h, boundary[i])
        expected = Counter({i: 1})
        if ty == STAR:
            expected[0] -= 1
        assert signed(expected, dh) == hd
        entries += 1
    return entries


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    for n in range(1, 6):
        entries = fan(n, 5, n in (2,3), emitter if n == 2 else None)
        print(f'F{n}: checked dh+hd on {entries} generators through rank four.')
    print('Checked both five-cell directions on two fans at inactive powers 0, 1 and 5.')
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Fourth inverse comparison in both directions at the first rim anchor.'))
