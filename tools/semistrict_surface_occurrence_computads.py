"""Unfold the literal occurrences and attaching types of a raw CaTT term."""
from argparse import ArgumentParser
from collections import Counter
from itertools import product
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, infer, maximal_vars, src, sub_from,
                  subst_tm, subst_ty, tdim, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_hidden_seam import identity


def unfold(ctx, term):
    """Return the occurrence context, its universal term, and its fold to ctx."""
    parent, types, old = [], [], []

    def root(i):
        while i != parent[i]:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    def match_type(a, b):
        assert a[0] == b[0]
        if a != STAR:
            match_type(a[1], b[1])
            match_term(a[2], b[2])
            match_term(a[3], b[3])

    def match_term(a, b):
        assert a[0] == b[0]
        if a[0] == 'v':
            i, j = sorted((root(a[1]), root(b[1])))
            if i != j:
                assert old[i] == old[j]
                parent[j] = i
                match_type(types[i], types[j])
        else:
            assert a[1:3] == b[1:3]
            for x, y in zip(a[3], b[3], strict=True):
                match_term(x, y)

    def fresh(t):
        if t[0] == 'v':
            label = t[1]
            original_type = ctx[label]
            ty = STAR
            if original_type != STAR:
                s, s_ty = fresh(original_type[2])
                u, u_ty = fresh(original_type[3])
                match_type(s_ty, u_ty)
                ty = arr(s_ty, s, u)
            index = len(parent)
            parent.append(index)
            types.append(ty)
            old.append(label)
            return v(index), ty

        _, arity, result_type, arguments = t
        lifted = []
        for declared, argument in zip(arity, arguments, strict=True):
            value, ty = fresh(argument)
            match_type(ty, subst_ty(declared, lifted))
            lifted.append(value)
        lifted = tuple(lifted)
        return ('coh', arity, result_type, lifted), subst_ty(result_type, lifted)

    expression, _ = fresh(term)
    reps = [i for i in range(len(parent)) if root(i) == i]
    numbered = {i: v(j) for j, i in enumerate(reps)}
    quotient = tuple(numbered[root(i)] for i in range(len(parent)))
    shape = tuple(subst_ty(types[i], quotient) for i in reps)
    universal = subst_tm(expression, quotient)
    fold = tuple(v(old[i]) for i in reps)
    check_ctx(shape)
    assert subst_tm(universal, fold) == term
    assert subst_ty(infer(shape, universal), fold) == infer(ctx, term)
    return shape, universal, fold


def maps_over(shape, fold, upper, upper_fold):
    def extend(prefix):
        i = len(prefix)
        if i == len(shape):
            yield tuple(prefix)
            return
        ty = subst_ty(shape[i], prefix)
        for j, image in enumerate(upper_fold):
            if image == fold[i] and upper[j] == ty:
                yield from extend(prefix + [v(j)])
    return extend([])


def bubble_context(coloured):
    ctx = (STAR,)
    fold = [v(0)]
    wire = identity(ctx, v(0))
    empty = identity(ctx, wire)

    def declare(s, t, label):
        nonlocal ctx
        assert infer(ctx, s) == infer(ctx, t)
        term = v(len(ctx))
        ctx += (arr(infer(ctx, s), s, t),)
        fold.append(v(label))
        return term

    bubbles = []
    for _ in range(2 if coloured else 1):
        gate = declare(wire, wire, 1)
        birth = declare(empty, gate, 2)
        death = declare(gate, empty, 3)
        bubbles.append(comp2(ctx, 2, birth, death))
    pairs = {(i, j): comp2(ctx, 2, a, b) for i, a in enumerate(bubbles) for j, b in enumerate(bubbles)}
    changes = [(s, t, declare(a, b, 4)) for s, a in pairs.items() for t, b in pairs.items()
               if s[1] == t[0]]
    return ctx, tuple(fold), changes


def bracket(ctx, labels, right):
    a, b, c = labels
    if right:
        return comp2(ctx, 3, a, comp2(ctx, 3, b, c))
    return comp2(ctx, 3, comp2(ctx, 3, a, b), c)


def check(emitter):
    base, _, [(_, _, z)] = bubble_context(False)
    upper, upper_fold, changes = bubble_context(True)
    expected = {tuple(k[2] for k in path) for path in product(changes, repeat=3)
                if path[0][1] == path[1][0] and path[1][1] == path[2][0]}
    assert len(expected) == 32
    chart = tree_ctx(string_tree(3, [4, 4, 4]))
    slots = maximal_vars(chart)
    axes = tuple(map(v, slots))
    assoc = head(chart, bracket(chart, axes, False), bracket(chart, axes, True))
    for right in (False, True):
        original = bracket(base, [z] * 3, right)
        shape, universal, fold = unfold(base, original)
        ranks = Counter(tdim(ty) + 1 for ty in shape)
        assert ranks == {0: 1, 2: 8, 3: 16, 4: 3}
        tips = [i for i, ty in enumerate(shape) if tdim(ty) + 1 == 4]
        terms = tuple(map(v, tips))
        assert universal == bracket(shape, terms, right)
        lifts = list(maps_over(shape, fold, upper, upper_fold))
        assert len(lifts) == len(expected)
        assert {tuple(f[i] for i in tips) for f in lifts} == expected
        assert {subst_tm(universal, f) for f in lifts} == {bracket(upper, path, right) for path in expected}
        sigma = sub_from(chart, shape, dict(zip(slots, terms, strict=True)))
        comparison = subst_tm(assoc, sigma)
        assert (src(shape, comparison), tgt(shape, comparison)) == (
            bracket(shape, terms, False), bracket(shape, terms, True))
        tag = 'right' if right else 'left'
        emitter.check_type(tag, shape, comparison, infer(shape, comparison))
        old_sigma = sub_from(chart, base, dict.fromkeys(slots, z))
        emitter.check_eq(tag + 'Fold', comparison, fold, subst_tm(assoc, old_sigma))
    print('Both universal bracketings have ranks (1,0,8,16,3); all 32 composable labelled triples lift uniquely.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    check(emitter)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('OccurrenceComputads', __doc__).replace('open import CaTTExp.Pure',
                                                                        'open import CaTTExp.Gray.Pure')
        (args.agda_dir / 'OccurrenceComputads.agda').write_text(module)
