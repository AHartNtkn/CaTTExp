"""Compute the usable spatial occurrences at two written path boundaries."""
from argparse import ArgumentParser
from collections import defaultdict
from functools import cache
from pathlib import Path

from catt import STAR, arr, comp2, infer, src, subst_tm, subst_ty, tdim, tgt, v
from ct_suspension import ident
from semistrict_surface_boundary_corridors import raw_lifter
from semistrict_surface_inverse_completion import DerivationEmitter


def step(word, rules):
    for s, t in rules:
        for i in range(len(word) - len(s) + 1):
            if word[i:i + len(s)] == s:
                yield word[:i] + t + word[i + len(s):]


def reachable(start, rules, within=lambda word: True):
    seen, todo = {start}, [start]
    while todo:
        for w in step(todo.pop(), rules):
            if within(w) and w not in seen:
                seen.add(w)
                todo.append(w)
    return seen


def windows(first, last, rules, weights):
    def weight(word):
        return sum(weights[c] for c in word)
    assert all(value > 0 for value in weights.values())
    assert all(weight(s) == weight(t) for s, t in rules)
    forward = reachable(first, rules)
    backward = reachable(last, [(t, s) for s, t in rules])

    def offsets(p, q):
        assert weight(p) == weight(q)
        return {weight(w[:i]) for w in forward for i in range(len(w) - len(p) + 1)
                if w[i:i + len(p)] == p and w[:i] + q + w[i + len(p):] in backward}
    return offsets


def check_monotone():
    candidates = [('', 'a'), ('a', 'ab'), ('a', 'b'), ('a', 'c'), ('b', 'bb'), ('c', 'cc')]
    for mask in range(1 << len(candidates)):
        chosen = [rule for i, rule in enumerate(candidates) if mask & (1 << i)]
        for first, last, rules in [('a', 'abb', chosen), ('abb', 'a', [(t, s) for s, t in chosen])]:
            limit = max(len(first), len(last))
            forward = reachable(first, rules, lambda w: len(w) <= limit)
            backward = reachable(last, [(t, s) for s, t in rules], lambda w: len(w) <= limit)
            observed = {rule for rule in rules for w in forward if any(t in backward for t in step(w, [rule]))}

            @cache
            def successes(w):
                # The sample rules strictly change length or replace a by b/c
                # (the reverse family reverses both orders), so this is finite.
                paths = {frozenset()} if w == last else set()
                for rule in rules:
                    for t in step(w, [rule]):
                        if len(t) <= limit:
                            paths.update(path | {rule} for path in successes(t))
                return paths

            assert observed == set().union(*successes(first))
            successes.cache_clear()


def check(emitter):
    check_monotone()
    weights = dict(a=1, b=1, h=2)
    rules = [('ab', 'h'), ('ab', 'ba')]
    offsets = windows('abab', 'abh', rules, weights)
    assert offsets('ab', 'h') == {2} and offsets('ab', 'ba') == set()
    assert offsets('a', 'a') == {0, 2} and offsets('h', 'h') == {2}
    # Positions can be at unequal letter indices at the same spatial weight.
    both = windows('abab', 'hh', rules, weights)
    assert both('ab', 'h') == {0, 2} and both('', '') == set(range(5))
    assert both('ba', 'ba') == {1}
    assert both('b', 'b') == {1, 3}

    old = ()

    def declare(ty):
        nonlocal old
        x = v(len(old))
        old += (ty,)
        return x

    x = declare(STAR)
    a, b, h = [declare(arr(STAR, x, x)) for _ in weights]
    ab, ba = comp2(old, 0, a, b), comp2(old, 0, b, a)

    def arrow(s, t):
        assert infer(old, s) == infer(old, t)
        return declare(arr(infer(old, s), s, t))

    p, q = [arrow(ab, h) for _ in range(2)]
    s = arrow(ab, ba)
    junk = arrow(comp2(old, 1, s, ident(old, ba)), s)
    z, r = [arrow(p, q) for _ in range(2)]
    stay, change = arrow(z, z), arrow(z, r)
    upper_left = comp2(old, 3, stay, change)
    u, u2 = [arrow(upper_left, change) for _ in range(2)]
    top = arrow(u, u2)

    alphabet = {a: 'a', b: 'b', h: 'h'}

    def word(t):
        if t[0] == 'v':
            return alphabet[t]
        return ''.join(word(label) for ty, label in zip(t[1], t[3], strict=True) if tdim(ty) == 0)

    def grade(t):
        s = target = t
        while tdim(infer(old, s)) + 1 > 1:
            s, target = src(old, s), tgt(old, target)
        return ('', '') if infer(old, s) == STAR else (word(s), word(target))

    grades = [grade(v(i)) for i in range(len(old))]
    declared_rules = [value for ty, value in zip(old, grades, strict=True) if tdim(ty) + 1 == 2]
    assert set(declared_rules) == set(rules)
    offsets = windows('abab', 'abh', declared_rules, weights)
    ctx = ()
    copies = defaultdict(list)
    names = {}
    fold = []
    for i, (ty, (before, after)) in enumerate(zip(old, grades, strict=True)):
        name = v(i)
        for offset in sorted(offsets(before, after)):
            if ty == STAR:
                lifted_ty = STAR
            elif tdim(ty) == 0:
                end = offset + weights[before]
                lifted_ty = arr(STAR, names[x, offset], names[x, end])
            else:
                lift = raw_lifter(ctx, copies)
                # A lifted 1-pole starts at the vertex for this weighted offset.
                def starts_here(cell):
                    while infer(ctx, cell) != STAR:
                        cell = src(ctx, cell)
                    return cell == names[x, offset]

                ls, = [s for s in lift(ty[2]) if starts_here(s)]
                lt, = [t for t in lift(ty[3]) if starts_here(t)]
                assert infer(ctx, ls) == infer(ctx, lt)
                lifted_ty = arr(infer(ctx, ls), ls, lt)
            assert subst_ty(lifted_ty, tuple(fold)) == ty
            local = v(len(ctx))
            copies[name].append(local)
            names[name, offset] = local
            fold.append(name)
            ctx += (lifted_ty,)
    assert not copies[s] and not copies[junk]
    assert all(ty[2][0] == ty[3][0] == 'v' for ty in ctx if 3 <= tdim(ty) + 1 <= 4)
    assert len(copies[change]) == len(copies[u]) == len(copies[top]) == 1
    lift = raw_lifter(ctx, copies)
    for tag, name in [('five', u), ('six', top)]:
        query = comp2(old, 0, ab, name)
        lifted, = lift(query)
        assert subst_tm(lifted, tuple(fold)) == query
        assert lift(src(old, query)) == (src(ctx, lifted),)
        assert lift(tgt(old, query)) == (tgt(ctx, lifted),)
        if emitter:
            emitter.check_type(tag + 'AtWindow', ctx, lifted, infer(ctx, lifted))
            emitter.check_type(tag + 'AtOriginalPoles', old, query, infer(old, query))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = DerivationEmitter() if args.agda_dir else None
    check(emitter)
    if emitter:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('WeightedWindows', __doc__).replace(
            'open import CaTTExp.Pure\n', 'open import CaTTExp.Gray.Pure\n'
            'open import CaTTExp.Pure using (∅)\n'
            'open import CaTTExp.PastingCheck ∅ using () renaming (checkPs to pastable)\n')
        (args.agda_dir / 'WeightedWindows.agda').write_text(module)
    print('Checked weighted windows, compound two-cell attachments, and exact lifts in degrees five and six.')


if __name__ == '__main__':
    main()
