"""Validate lower walking-equivalence attachments and the two machine interfaces."""
from argparse import ArgumentParser
from itertools import permutations
from pathlib import Path

from catt import (STAR, arr, check_ctx, coh_between, comp2, disc_tree, infer, src, sub_from,
                  subst_tm, subst_ty, tdim_tm, tgt, tree_ctx, v)
from ct_suspension import susp_ctx
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_odd_cubes import walking_piece
from semistrict_surface_scalar_cube import exchange


def compare_on_disc(ctx, term, left, right):
    degree = tdim_tm(ctx, term)
    tree = disc_tree(degree)
    disc = tree_ctx(tree)
    generic = v(len(disc) - 1)
    witness = coh_between(disc, tree, [generic], left(disc, generic), right(disc, generic))
    return subst_tm(witness, sub_from(disc, ctx, {len(disc) - 1: term}))


def right_unit(ctx, a):
    return comp2(ctx, tdim_tm(ctx, a) - 1, a, identity(ctx, tgt(ctx, a)))


def unchanged(ctx, a):
    return a


def attach_copy(ctx, seed, cap):
    rank = tdim_tm(ctx, seed)
    depth = cap - rank
    presentation = walking_piece(depth) if depth else (STAR, STAR)
    for _ in range(rank):
        presentation = susp_ctx(presentation)
    disc_end = 2 * rank
    sigma = sub_from(presentation[:disc_end + 1], ctx, {disc_end: seed})
    result = list(ctx)
    fresh = v(len(ctx))
    for ty in presentation[disc_end + 1:]:
        instantiated = subst_ty(ty, sigma)
        sigma += (v(len(result)),)
        result.append(instantiated)
    check_ctx(tuple(result))
    assert result[fresh[1]] == infer(ctx, seed)
    return tuple(result), fresh


def check_cylinders(em):
    counts = []
    for cap in (2, 3, 4):
        base = (STAR,)
        unit = identity(base, v(0))
        first, f = attach_copy(base, unit, cap)
        # f -> 1 is an inverse-direction generator in the suspended walk.
        back = v(f[1] + 2)
        ff = comp2(first, 0, f, f)
        fit = compare_on_disc(first, f, right_unit, unchanged)
        seed = comp2(first, 1, comp2(first, 0, f, back), fit)
        second, a = attach_copy(first, seed, cap)
        expected = arr(infer(first, f), ff, f)
        em.check_type(f'oldAttach{cap}', second, a, expected)
        em.check_type(f'oldChoice{cap}', second, seed, expected)
        histogram = [sum(tdim_tm(second, v(i)) == d for i in range(len(second)))
                     for d in range(1, cap + 1)]
        assert histogram == [sum(1 if d == n else 3 * 2 ** (d - n - 1)
                                 for n in (1, 2) if n <= d) for d in range(1, cap + 1)]
        counts.append(histogram)
    return counts


def check_gate(em, k):
    m = k - 2
    if k == 3:
        loop = arr(STAR, v(0), v(0))
        ctx = (STAR, loop, arr(loop, v(1), v(1)))
        crossing = exchange(ctx, v(2), v(2))
        s, t = tgt(ctx, crossing), src(ctx, crossing)
    else:
        disc = tree_ctx(disc_tree(k - 1))
        ctx = disc + (disc[-1],)
        s, t = v(len(disc) - 1), v(len(disc))
    b = tgt(ctx, s)
    ty = infer(ctx, b)

    def declare(ty):
        nonlocal ctx
        name = v(len(ctx))
        ctx += (ty,)
        return name

    h = declare(ty)
    opening, closing = declare(arr(ty, b, h)), declare(arr(ty, h, b))
    start, digit, accept, pass_h = [declare(arr(ty, h, h)) for _ in range(4)]
    pass_b = declare(arr(ty, b, b))
    word = comp2(ctx, m, start, digit)

    def wrap(tape):
        return comp2(ctx, m, comp2(ctx, m, opening, tape), closing)

    def rule(left, right):
        assert infer(ctx, left) == infer(ctx, right)
        return declare(arr(infer(ctx, left), left, right))

    init_b = rule(identity(ctx, b), wrap(word))
    init_h = rule(identity(ctx, h), word)
    step = rule(word, accept)
    exit_b, exit_h = rule(wrap(accept), pass_b), rule(accept, pass_h)
    guarded = rule(comp2(ctx, m, s, pass_b), t)
    check_ctx(ctx)

    def run(first, middle, last):
        return comp2(ctx, k - 1, comp2(ctx, k - 1, first, middle), last)

    permit = run(init_b, wrap(step), exit_b)
    open_permit = run(init_h, step, exit_h)
    fitted = compare_on_disc(ctx, s, unchanged, right_unit)
    literal = run(fitted, comp2(ctx, m, s, permit), guarded)
    em.check_type(f'openPass{k}', ctx, open_permit, arr(infer(ctx, pass_h), identity(ctx, h), pass_h))
    em.check_type(f'closedPass{k}', ctx, permit, arr(infer(ctx, pass_b), identity(ctx, b), pass_b))
    em.check_type(f'originalBoundary{k}', ctx, literal, arr(infer(ctx, s), s, t))


def check_sessions(bit, bound):
    # Wire matching for a closed diagram is a multiset of directed words.
    # Enumerate insertions anywhere on a wire, disjoint starts, and all program
    # rewrites before the first exit. Insertions are bounded for this finite check.
    initial = 'LX' + bit + 'R'
    ready = 'LAR'
    rules = [('X0', '0Y'), ('X1', '1Z'), ('0YR', 'AR'), ('1ZR', '1NR')]
    plain = {initial}
    current = initial
    for left, right in rules:
        if left in current:
            current = current.replace(left, right, 1)
            plain.add(current)
    seen = {()}
    pending = [()]
    insertions = updates = exits = 0
    while pending:
        words = pending.pop()
        total = sum(w.count('L') for w in words)
        candidates = []
        if total < bound:
            candidates.append((*words, initial))
            insertions += 1
        for i, word in enumerate(words):
            stack = []
            for letter in word:
                if letter == 'L':
                    stack.append([])
                elif letter == 'R':
                    assert 'L' + ''.join(stack.pop()) + 'R' in plain
                else:
                    stack[-1].append(letter)
            assert not stack
            others = words[:i] + words[i + 1:]
            if total < bound:
                for j in range(len(word) + 1):
                    candidates.append((*others, word[:j] + initial + word[j:]))
                    insertions += 1
            for left, right in rules:
                for j in range(len(word)):
                    if word.startswith(left, j):
                        candidates.append((*others, word[:j] + right + word[j + len(left):]))
                        updates += 1
            exits += word.count(ready)
        for candidate in candidates:
            canonical = tuple(sorted(candidate))
            if canonical not in seen:
                pending.append(canonical)
                seen.add(canonical)
    assert bool(exits) == (bit == '0')
    return len(seen), insertions, updates, exits


def check_matchings():
    # Independent strand renamings at a cut cancel on gluing. Rewiring just
    # one side can give a different closed multiset when labels differ.
    prefixes, suffixes = ('LA', 'LB', 'LC'), ('1R', '2R', '3R')
    outputs = set()
    for match in permutations(range(3)):
        joined = tuple(sorted(prefixes[i] + suffixes[match[i]] for i in range(3)))
        for perm in permutations(range(3)):
            outgoing = {perm[i]: suffixes[match[i]] for i in range(3)}
            renamed = tuple(sorted(prefixes[i] + outgoing[perm[i]] for i in range(3)))
            assert renamed == joined
            if perm != (0, 1, 2):
                assert tuple(sorted(prefixes[i] + outgoing[i] for i in range(3))) != joined
        outputs.add(joined)
    assert len(outputs) == 6


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    check_matchings()
    for bit in '01':
        print('Input, closed diagrams, insertions, updates, available exits:', bit, *check_sessions(bit, 3))
    em = Emitter()
    print('Walking attachment rank counts:', check_cylinders(em))
    for k in (3, 4, 5):
        check_gate(em, k)
    if args.agda_dir:
        for prefix, kernel in [('Ordinary', 'CaTTExp.Pure'), ('Gray', 'CaTTExp.Gray.Pure')]:
            name = prefix + 'FirstFailureGate'
            body = em.module(name, __doc__).replace('open import CaTTExp.Pure\n', f'open import {kernel}\n')
            (args.agda_dir / (name + '.agda')).write_text(body)
