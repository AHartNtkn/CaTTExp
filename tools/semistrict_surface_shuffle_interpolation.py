"""Decide two-site shuffle comparisons from finite local path tables."""
from argparse import ArgumentParser
from collections import deque
from functools import cache
from itertools import product
from pathlib import Path


def reachable(start, successors):
    seen = {start}
    pending = deque(seen)
    while pending:
        for nxt in successors(pending.popleft()):
            if nxt not in seen:
                seen.add(nxt)
                pending.append(nxt)
    return seen


class Site:
    """Typed local generators and a finite supply of partner representatives."""

    def __init__(self, edges, rules, representatives, leq):
        self.edges = edges
        self.rules = rules
        self.representatives = representatives
        self.leq = leq

    def vertices(self, start, word):
        result = [start]
        for letter in word:
            source, target = self.edges[letter]
            assert result[-1] == source
            result.append(target)
        return result


def split(word, probe):
    """Local segments and the projected local prefix length at every cut."""
    segments = ['']
    for letter in word:
        if probe(letter):
            segments.append('')
        else:
            segments[-1] += letter.lower()
    cuts = [0]
    for segment in segments:
        cuts.append(cuts[-1] + len(segment))
    return segments, cuts


def interpolate(source, target, left, right, starts=(0, 0)):
    u, source_cuts = split(source, str.isupper)
    n, target_cuts = split(target, str.islower)
    a = ''.join(c for c in target if c.islower())
    b = ''.join(c.lower() for c in source if c.isupper())
    ls = left.vertices(starts[0], ''.join(u))
    lt = left.vertices(starts[0], a)
    rs = right.vertices(starts[1], b)
    rt = right.vertices(starts[1], ''.join(n))
    assert ls[-1] == lt[-1] and rs[-1] == rt[-1]

    @cache
    def visit(i, j, last_i, last_j, d, e):
        # i,j count letters of the intermediate shuffle already chosen.
        # last_i is the left cut at the last right letter, and conversely.
        if (i, j) == (len(a), len(b)):
            return (left.leq(ls[source_cuts[j]], u[j], d + a[last_i:i])
                    and right.leq(rt[target_cuts[i]], e + b[last_j:j], n[i]))
        if j < len(b):
            for nxt in left.representatives.get((ls[source_cuts[j+1]], lt[i]), ()):
                if (left.leq(ls[source_cuts[j]], u[j] + nxt, d + a[last_i:i])
                        and visit(i, j+1, i, last_j, nxt, e)):
                    return True
        if i < len(a):
            for nxt in right.representatives.get((rt[target_cuts[i+1]], rs[j]), ()):
                if (right.leq(rt[target_cuts[i]], e + b[last_j:j], n[i] + nxt)
                        and visit(i+1, j, last_i, j, d, nxt)):
                    return True
        return False

    return visit(0, 0, 0, 0, '', '')


def direct_moves(word, sites, starts, limit):
    """All literal substring rewrites, including births at typed cuts."""
    states = list(starts)
    for i in range(len(word) + 1):
        for color, site in enumerate(sites):
            for pole, old, new in site.rules:
                if states[color] != pole or len(word) - len(old) + len(new) > limit:
                    continue
                if color:
                    old, new = old.upper(), new.upper()
                if word.startswith(old, i):
                    yield word[:i] + new + word[i+len(old):]
        if i < len(word):
            first = word[i]
            if first.isupper() and i+1 < len(word) and word[i+1].islower():
                yield word[:i] + word[i+1] + first + word[i+2:]
            color = int(first.isupper())
            s, t = sites[color].edges[first.lower()]
            assert states[color] == s
            states[color] = t


def acyclic_site(rules):
    edges = dict(a=(0, 1), b=(0, 1), c=(1, 2), d=(1, 2), h=(0, 2))
    reps = {}
    for start in range(3):
        def paths(at, word):
            reps.setdefault((start, at), []).append(word)
            for letter, (s, t) in edges.items():
                if at == s:
                    paths(t, word + letter)
        paths(start, '')

    @cache
    def closure(start, word):
        def moves(w):
            vertices = site.vertices(start, w)
            for i, vertex in enumerate(vertices):
                for s, old, new in rules:
                    if vertex == s and w.startswith(old, i):
                        yield w[:i] + new + w[i+len(old):]
        return reachable(word, moves)

    site = Site(edges, rules, reps, lambda s, w, v: v in closure(s, w))
    return site


def idempotent_site(birth, death):
    rules = [(0, 'xx', 'x'), (0, 'x', 'xx')]
    if birth:
        rules.append((0, '', 'x'))
    if death:
        rules.append((0, 'x', ''))
    return Site({'x': (0, 0)}, rules, {(0, 0): ['', 'x']},
                lambda _, w, v: bool(w) == bool(v) or (birth if v else death))


def shuffles(u, v):
    if not u or not v:
        yield u + v
        return
    for tail in shuffles(u[1:], v):
        yield u[0] + tail
    for tail in shuffles(u, v[1:]):
        yield v[0] + tail


def compare(words, left, right, limit):
    positive = 0
    for source in words:
        actual = reachable(source, lambda w: direct_moves(w, (left, right), (0, 0), limit))
        for target in words:
            decision = interpolate(source, target, left, right)
            assert decision == (target in actual), (source, target, decision)
            positive += decision
    return len(words)**2, positive


def emit_kernel_example(directory):
    from catt import STAR, arr, check_ctx, comp2, infer, v
    from emit_agda import Emitter
    from semistrict_surface_scalar_cube import exchange

    left, right = arr(STAR, v(0), v(1)), arr(STAR, v(1), v(2))
    f, g = v(3), v(4)
    lf, rg = arr(left, f, f), arr(right, g, g)
    a, updated_a, b, updated_b, alpha, beta = map(v, range(5, 11))
    ctx = ((STAR,) * 3 + (left, right, lf, lf, rg, rg)
           + (arr(lf, a, updated_a), arr(rg, b, updated_b)))
    check_ctx(ctx)

    def then(x, y):
        return comp2(ctx, 1, x, y)

    def left_event(x):
        return comp2(ctx, 0, x, g)

    def right_event(x):
        return comp2(ctx, 0, f, x)

    r = right_event(b)
    start = then(then(r, left_event(a)), r)
    end = then(then(left_event(updated_a), right_event(updated_b)), r)
    update_left = then(then(r, left_event(alpha)), r)
    cross = then(exchange(ctx, updated_a, b), r)
    update_right = then(then(left_event(updated_a), right_event(beta)), r)
    witness = comp2(ctx, 2, comp2(ctx, 2, update_left, cross), update_right)
    expected = arr(infer(ctx, start), start, end)
    assert infer(ctx, witness) == expected
    emitter = Emitter()
    emitter.check_type('twoPhases', ctx, witness, expected)
    name = 'GrayShuffleInterpolation'
    module = emitter.module(name, __doc__).replace('open import CaTTExp.Pure\n',
                                                   'open import CaTTExp.Gray.Pure\n')
    (directory / (name + '.agda')).write_text(module)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    if args.agda_dir:
        emit_kernel_example(args.agda_dir)
    totals = [0, 0]
    cases = [(), ((0, 'a', 'b'), (1, 'd', 'c'), (0, 'bc', 'h')),
             ((0, 'h', 'ad'), (0, 'a', 'b'), (0, 'bc', 'h'))]
    for lrules, rrules in product(cases, repeat=2):
        left, right = acyclic_site(lrules), acyclic_site(rrules)
        words = [w for u in left.representatives[0, 2]
                 for v in right.representatives[0, 2] for w in shuffles(u, v.upper())]
        counts = compare(words, left, right, 4)
        totals = [a+b for a, b in zip(totals, counts)]
    print(f'Typed acyclic sites: {totals[0]} judgments, {totals[1]} reachable')
    totals = [0, 0]
    words = [''.join(w) for k in range(4) for w in product('xX', repeat=k)]
    for lb, ld, rb, rd in product((False, True), repeat=4):
        counts = compare(words, idempotent_site(lb, ld), idempotent_site(rb, rd), 8)
        totals = [a+b for a, b in zip(totals, counts)]
    print(f'Idempotent sites with optional births and deaths: {totals[0]} judgments, '
          f'{totals[1]} reachable')


if __name__ == '__main__':
    main()
