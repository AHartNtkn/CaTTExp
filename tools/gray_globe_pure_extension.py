"""Construct actual CaTT terms when the pure factors of a globe-pair core grow."""
import argparse
from collections import Counter
from itertools import product
from pathlib import Path

from canonical_gray_two_discs import strict_interpreter
from catt import (check_ctx, comp2, fv_tm, infer, maximal_vars, subst_tm, subst_ty,
                  tree_of, v)
from emit_agda import Emitter
from gray_globe_attachments import ordered_factors
from gray_globe_comparison import atom, face, globe
from gray_globe_factorizations import hole_split, profile, rank
from gray_globe_section import cells, row_map
from gray_globe_sector_terms import arrow, pure_type, verify
from rc2 import functor


def raise_argument(ctx, term, variable, higher):
    """Apply a top-dimensional term in one occurrence to a cell over that slot."""
    assert infer(ctx, higher)[2] == variable
    if term == variable:
        return higher
    _, arity, ty, sigma = term
    slots = maximal_vars(arity)
    active, = (s for s in slots if variable[1] in fv_tm(sigma[s]))
    raised = raise_argument(ctx, sigma[active], variable, higher)
    head = ('coh', arity, ty, tuple(map(v, range(len(arity)))))
    result = functor(ctx, None, arity, tree_of(arity), head,
                     {s: sigma[s] for s in slots}, {active: raised})
    assert infer(ctx, result)[2] == term
    return result


def two_by_two():
    """Complete the edge section on the core, including its single top atom."""
    ctx, names, chosen = verify(2, 2, None)
    top_label = ((2, 2), (2, 2))
    top = atom(top_label)
    names[top_label] = chosen[top] = v(len(ctx))
    ctx += (arrow(ctx, *(chosen[face(top, s)] for s in (0, 1))),)
    for c in cells((2, 2)) - {()} - chosen.keys():
        (a, b), = hole_split(c, 1, 1)
        chosen[c] = comp2(ctx, 0, chosen[a], chosen[b])
    return ctx, names, chosen


def extend(data, shape, axis, new_rank, emitter):
    previous, generators, terms = data
    old_rank = shape[axis]
    if new_rank == old_rank:
        return data
    shape = list(shape)
    shape[axis] = new_rank
    ctx, names, chosen = (), {}, {}

    for tag in (0, 1):
        def embed(g):
            if g[axis][0] != old_rank:
                return g
            h = list(g)
            h[axis] = (old_rank, tag)
            return tuple(h)

        sigma = []
        for g, ty in zip(generators, previous):
            h = embed(g)
            wanted = subst_ty(ty, sigma)
            if h not in names:
                names[h] = v(len(ctx))
                ctx += (wanted,)
            assert infer(ctx, names[h]) == wanted
            sigma.append(names[h])
        for c, t in terms.items():
            h, term = row_map(c, 0, embed), subst_tm(t, sigma)
            if h in chosen:
                assert chosen[h] == term
            chosen[h] = term

    labels = product(*(globe(d) for d in shape))
    for g in sorted(labels, key=lambda h: sum(rank(h))):
        if rank(g)[axis] > old_rank and rank(g)[1-axis] == 0:
            names[g] = v(len(ctx))
            ctx += (pure_type(ctx, names, g),)
    check_ctx(ctx)
    allowed = set(map(rank, names))
    domain = {c: profile(c) for c in cells(tuple(shape)) if c}
    domain = {c: ranks for c, ranks in domain.items() if ranks <= allowed}
    counts = Counter()
    emitted = set()
    for c in sorted(domain.keys()-chosen.keys(), key=lambda t: (len(t), len(domain[t]), t)):
        cut = old_rank
        owner = {p: int(p[axis] <= cut) for p in domain[c] if sum(p) > cut}
        factors = ordered_factors(c, cut, owner)
        if len(factors) == 2:
            a, b = factors
            term, kind = comp2(ctx, cut, chosen[a], chosen[b]), 'paste'
        else:
            assert factors == (c,)
            label, = c[-1][0]
            before, = face(atom(label), 0)[-1][0]
            term = raise_argument(ctx, chosen[face(c, 0)], names[before], names[label])
            kind = 'atom' if term[0] == 'v' else 'raise'
        wanted = arrow(ctx, *(chosen[face(c, s)] for s in (0, 1)))
        assert infer(ctx, term) == wanted
        chosen[c] = term
        counts[kind] += 1
        key = kind, len(c)
        if emitter and kind != 'atom' and key not in emitted:
            emitter.check_type(f'axis-{axis}-{kind}-{len(c)-1}', ctx, term, wanted)
            emitted.add(key)
    print(f'Extended axis {axis} from {old_rank} to {new_rank}: {dict(counts)}')
    return ctx, names, chosen


def check(data):
    ctx, names, terms = data
    evaluate = strict_interpreter(ctx, tuple(names))
    check_ctx(ctx)
    assert all(terms[atom(g)] == t for g, t in names.items())
    for c, t in terms.items():
        assert evaluate(t) == c
        if len(c) > 1:
            assert infer(ctx, t)[2:] == tuple(terms[face(c, s)] for s in (0, 1))
    print(f'Checked {len(terms)} terms and {len(names)} generator pins')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if min(args.m, args.n) < 2:
        parser.error('the sample core has dimensions (2,2)')
    emitter = Emitter() if args.agda else None
    base = two_by_two()
    check(base)
    left = extend(base, (2, 2), 0, args.m, emitter)
    result = extend(left, (args.m, 2), 1, args.n, emitter)
    check(result)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'From tools/gray_globe_pure_extension.py.'))
