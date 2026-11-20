"""Construct partial naturality cells on marked leaves of a globular pasting arity."""
import argparse
from functools import cache
from itertools import combinations
from pathlib import Path

from catt import (arr, comp2, fv_tm, fv_ty, infer, is_ps, maximal_vars, restrict,
                  src, subst_tm, subst_ty, tdim_tm, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_exterior_actions import certificate, chart_preimage, coherence


def marked_leaves(old, marks):
    assert marks and marks <= set(maximal_vars(old))
    ctx, minus, plus, changes = (), [], [], {}
    for i, ty in enumerate(old):
        a = subst_ty(ty, minus)
        assert a == subst_ty(ty, plus)
        x = v(len(ctx))
        ctx += (a,)
        minus.append(x)
        if i in marks:
            y, h = v(len(ctx)), v(len(ctx) + 1)
            ctx += (a, arr(a, x, y))
            changes[i] = h
            plus.append(y)
        else:
            plus.append(x)
    assert is_ps(ctx)

    @cache
    def support(w):
        return fv_tm(w) | fv_ty(infer(old, w))

    @cache
    def lift(w):
        selected = support(w) & marks
        if not selected:
            return None
        if w[0] == 'v':
            return changes[w[1]]

        a, b = subst_tm(w, minus), subst_tm(w, plus)
        sources, targets = [], []
        s = t = w
        for _ in range(tdim_tm(old, w)):
            s, t = src(old, s), tgt(old, t)
            sources.append(s)
            targets.append(t)
        for i, (s, t) in enumerate(zip(reversed(sources), reversed(targets))):
            hs, ht = lift(s), lift(t)
            if ht is not None:
                a = comp2(ctx, i, a, ht)
            if hs is not None:
                b = comp2(ctx, i, hs, b)

        # Use the promoted support of the old pole, including every marked
        # connector, even when that connector is below the dimension of w.
        used = {end[i][1] for i in support(w) for end in (minus, plus)}
        used.update(changes[i][1] for i in selected)
        local, inclusion = restrict(ctx, used)
        assert is_ps(local)
        recover = chart_preimage(local, inclusion)
        l, r = recover(a), recover(b)
        assert l is not None and r is not None
        h = subst_tm(coherence(local, l, r), inclusion)
        assert infer(ctx, h) == arr(infer(ctx, a), a, b)
        assert fv_tm(h) | fv_ty(infer(ctx, h)) == used
        return h

    return ctx, lift


def check(max_height, emitter):
    count = 0
    for height in range(3, max_height + 1):
        # Two composable top cells in one branch, an independent edge
        # and an independent 2-cell on the other branches.
        branch = ((), ())
        for _ in range(height - 2):
            branch = (branch,)
        old = tree_ctx(((), branch, ((),)))
        w = ucomp(old)
        # Use an alternative full composite and an identity above it.
        alt = comp2(old, height - 1, w, ident(old, tgt(old, w)))
        comparison = coherence(old, w, alt)
        terms = (w, alt, comparison, ident(old, comparison))
        leaves = maximal_vars(old)
        assert len(leaves) == 4 and tdim_tm(old, w) == height
        for size in range(1, len(leaves) + 1):
            for subset in combinations(leaves, size):
                ctx, lift = marked_leaves(old, frozenset(subset))
                for term in terms:
                    result = lift(term)
                    assert tdim_tm(ctx, result) == tdim_tm(old, term) + 1
                    count += 1
                if emitter and height == max_height and set(subset) == {leaves[0], leaves[1]}:
                    certify = certificate(emitter, ctx)
                    certify('mixed-leaf-composite', lift(w), infer(ctx, lift(w)))
                    certify('mixed-leaf-coherence', lift(comparison), infer(ctx, lift(comparison)))
    print(f'Checked {count} leaf actions through arity height {max_height}.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('height', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.height < 3:
        parser.error('height must be at least three')
    out = Emitter() if args.agda else None
    check(args.height, out)
    if out:
        args.agda.write_text(out.module(args.agda.stem, 'Partial naturality at independent leaves.'))
