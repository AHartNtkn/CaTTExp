"""Recover the first incomplete diagonal of a globe pair from smaller signed rectangles."""
import argparse
from collections import Counter, defaultdict
from functools import cache
from pathlib import Path

from canonical_gray_two_discs import strict_interpreter
from catt import comp2, fv_tm, infer, subst_tm, v
from emit_agda import Emitter
from gray_globe_attachments import ordered_factors
from gray_globe_comparison import atom, face, globe
from gray_globe_corner_pullback import labelled_tableaux
from gray_globe_exterior_actions import certificate
from gray_globe_factorizations import hole_split, rank, truncate
from gray_globe_pure_extension import raise_argument
from gray_globe_section import EMPTY_ROW, cells
from gray_globe_sector_terms import arrow, boundary_bridge, verify
from gray_path_wedge import compose


@cache
def peak(m, n):
    return atom(((m, 2), (n, 2)))


def positions(m, n, d):
    return tuple(range(max(0, d-n), min(m, d)+1))


def runs(indices):
    groups = []
    for i in indices:
        if groups and groups[-1][1]+1 == i:
            groups[-1] = groups[-1][0], i
        else:
            groups.append((i, i))
    return tuple(groups)


def box(m, n, k, a, b):
    return (m if b == k+1 else b, n if a == 0 else k+1-a)


def replace_tag(g, axis, bound, tag):
    return tuple((i, tag) if j == axis and i == bound else (i, x)
                 for j, (i, x) in enumerate(g))


def restrict(c, m, n, k, a, b):
    u, v = box(m, n, k, a, b)
    def chain(labels):
        return tuple(replace_tag(replace_tag(g, 0, u, 2), 1, v, 2)
                     for g in labels if g[0][0] <= u and g[1][0] <= v)
    return peak(u, v)[:k] + tuple(tuple(chain(labels) for labels in row) for row in c[k:])


def extend(native, m, n, k, s, t):
    # Reinstall the frozen outer tags from the source k-row.
    a, b = (g[0][0] for g in (native[k+1][0][0], native[k+1][0][-1]))
    u, v = box(m, n, k, a, b)
    source = s[k][0]
    left = next((x for (i, x), _ in source if i == u), 2)
    right = next((y for _, (j, y) in source if j == v), 2)
    def include(g):
        return replace_tag(replace_tag(g, 0, u, left), 1, v, right)
    tail = tuple(tuple(tuple(include(g) for g in labels) for labels in row)
                 for row in native[k+1:])
    return s[:k] + ((source, t[k][0]),) + tail


def split(c, k, intervals):
    def owner(i, j):
        # Every upper site's whole shadow at k+1 is present.
        lo, hi = max(0, k+1-j), min(k+1, i)
        return next(a for a, b in intervals if a <= lo <= hi <= b)
    owners = {rank(g): owner(*rank(g)) for row in c[k+1:] for g in row[0]}
    return ordered_factors(c, k, owners)


def pins(m, n):
    result = set()
    for p in globe(m):
        for q in globe(n):
            g = atom((p, q))
            for d in range(len(g)):
                for side in (0, 1):
                    c = truncate(g, d, side)
                    u, v = min(d, p[0]), min(d, q[0])
                    smaller = tuple(tuple(tuple(replace_tag(replace_tag(label, 0, u, 2), 1, v, 2)
                                                for label in chain) for chain in row) for row in c)
                    assert smaller == truncate(peak(u, v), d, side)
                    result.add(c)
    return result


def previous_stage(m, n, k, a, b, s, t):
    """Isolate the moving block and test exactly which signed atom feeds its lower template."""
    u, v = box(m, n, k, a, b)
    cell = extend(peak(u, v), m, n, k, s, t)
    lo, hi = max(0, a-1), min(k, b)
    u1, v1 = box(m, n, k-1, lo, hi)
    assert u <= u1 and v <= v1 and (u1, v1) != (m, n)
    owners = {rank(g): (lo if d > k or lo <= g[0][0] <= hi else g[0][0])
              for d, row in enumerate(cell) if d >= k for g in row[0]}
    pieces = ordered_factors(cell, k-1, owners)
    active, = (x for x in pieces if len(x) > k+1)
    assert all(len(x[k][0]) == 1 for x in pieces if x != active)
    smaller = restrict(active, m, n, k-1, lo, hi)
    left = 2 if u == u1 else next(x for (i, x), _ in s[k][0] if i == u)
    right = 2 if v == v1 else next(y for _, (j, y) in s[k][0] if j == v)
    assert smaller == atom(((u, left), (v, right)))
    assert active == extend(smaller, m, n, k-1, *(truncate(active, k-1, j) for j in (0, 1)))
    for sign, end in enumerate((s, t)):
        state_parts = ordered_factors(end, k-1, owners)
        assert state_parts == tuple(truncate(x, k, sign) for x in pieces)


def check(m, n):
    @cache
    def domain(u, v):
        return set(labelled_tableaux(u, v))
    ambient = domain(m, n)
    if max(m, n) <= 5:
        assert ambient == cells((m, n)) - {()}
    pinned = pins(m, n)
    counts = Counter()
    actual = defaultdict(set)
    single = set()
    for c in ambient:
        for d, row in enumerate(c):
            active = tuple(g[0][0] for g in row[0])
            if active != positions(m, n, d):
                break
        else:
            counts['full object'] += 1
            assert c[:d] == peak(m, n)[:d]
            if d and d < m+n:
                steps = ordered_factors(c, d-1, {rank(g): g[0][0] for g in row[0]})
                assert len(steps) == len(row[0]) > 1
                word = steps[0]
                for step in steps[1:]:
                    word = compose(word, step, d-1)
                assert word == c
            continue
        k = d-1
        assert c[:k] == peak(m, n)[:k]
        groups = runs(active)
        pieces = split(c, k, groups) if len(groups) > 1 else (c,)
        assert len(pieces) == len(groups)
        if len(groups) > 1:
            assert c not in pinned
            counts['several runs'] += 1
        result = None
        for part, (a, b) in zip(pieces, groups, strict=True):
            u, v = box(m, n, k, a, b)
            assert u+v < m+n
            s, t = (truncate(part, k, side) for side in (0, 1))
            key = (k, a, b, s, t)
            smaller = restrict(part, m, n, k, a, b)
            assert smaller in domain(u, v)
            assert all(truncate(smaller, k, i) == truncate(peak(u, v), k, i) for i in (0, 1))
            rebuilt = extend(smaller, m, n, k, s, t)
            assert rebuilt == part
            actual[key].add(smaller)
            padded = len(s[k][0]) > len(smaller[k][0])
            if len(groups) == 1:
                counts['padded run' if padded else 'signed face'] += 1
                if padded:
                    assert c not in pinned
                    single.add(key)
            height = len(c)
            rebuilt += (EMPTY_ROW,)*(height-len(rebuilt))
            result = rebuilt if result is None else compose(result, rebuilt, k)
        assert result == c

    @cache
    def diagonal(u, v, k):
        poles = tuple(truncate(peak(u, v), k, i) for i in (0, 1))
        return {c for c in domain(u, v) if len(c) > k+1
                and tuple(truncate(c, k, i) for i in (0, 1)) == poles}

    for (k, a, b, s, t), native in actual.items():
        u, v = box(m, n, k, a, b)
        assert native == diagonal(u, v, k)
        for c in native:
            expanded = extend(c, m, n, k, s, t)
            assert expanded in ambient
            if len(c) > k+2:
                assert all(extend(face(c, i), m, n, k, s, t) == face(expanded, i)
                           for i in (0, 1))
    for key in single:
        previous_stage(m, n, *key)
    print(f'D^{m} tensor D^{n}: {len(ambient)} cells; {dict(sorted(counts.items()))}.')
    print('Padded endpoint pairs by (cut, run length):',
          dict(sorted(Counter((k, b-a+1) for k, a, b, _, _ in single).items())))


def term_check(m, n, emitter):
    """Use one formal arrow on each padded two-position run at cut two."""
    groups = defaultdict(list)
    for c in labelled_tableaux(m, n):
        if len(c) > 3 and len(c[2][0]) == 3:
            ranks = tuple(g[0][0] for g in c[3][0])
            if ranks in ((0, 1), (2, 3)):
                groups[tuple(truncate(c, 2, i) for i in (0, 1))].append(c)
    ctx, names, chosen = verify(m, n, None, required={x for ends in groups for x in ends})
    evaluate = strict_interpreter(ctx, tuple(names))
    certify = certificate(emitter, ctx) if emitter else None
    emitted = set()
    counts = Counter()
    for (s, t), family in groups.items():
        c = next(x for x in family if len(x) == 4)
        hole = (2, 1) if rank(c[3][0][0])[0] == 0 else (1, 2)
        parts, = hole_split(c, *hole)
        index = next(i for i, x in enumerate(parts) if len(x) == 4)
        prototype = chosen[parts[index]]
        formal = ctx + (infer(ctx, prototype),)
        slot = v(len(ctx))
        spatial = [chosen[x] for x in parts]
        spatial[index] = slot
        body = comp2(formal, 1, *spatial)
        raw_s, raw_t = infer(formal, body)[2:]
        before = boundary_bridge(ctx, evaluate, names, chosen[s], raw_s) if chosen[s] != raw_s else None
        after = boundary_bridge(ctx, evaluate, names, raw_t, chosen[t]) if chosen[t] != raw_t else None
        if before:
            body = comp2(formal, 2, before, body)
        if after:
            body = comp2(formal, 2, body, after)
        assert infer(formal, body) == arrow(ctx, chosen[s], chosen[t])
        assert slot[1] in fv_tm(body)
        if emitter and 'open' not in emitted:
            emitter.check_type('open-arrow', formal, body, infer(formal, body))
            emitted.add('open')

        levels = [body]
        assignments = {s: chosen[s], t: chosen[t]}
        for target in sorted(family, key=len):
            pair, = hole_split(target, *hole)
            native = chosen[pair[index]]
            while len(levels) < len(target)-3:
                # Grow only the formal top variable, keeping both of its old boundaries.
                fresh = v(len(formal))
                formal += (infer(formal, slot),)
                higher = v(len(formal))
                formal += (arrow(formal, slot, fresh),)
                levels.append(raise_argument(formal, levels[-1], slot, higher))
                slot = higher
            args = [native]
            while len(args) < 2*(len(target)-4)+1:
                args[0:0] = infer(ctx, args[0])[2:]
            sub = tuple(map(v, range(len(ctx)))) + tuple(args)
            term = subst_tm(levels[len(target)-4], sub)
            wanted = arrow(ctx, *(assignments[face(target, j)] for j in (0, 1)))
            assert infer(ctx, term) == wanted and evaluate(term) == target
            assignments[target] = term
            d = len(target)-1
            counts[d] += 1
            if certify and d not in emitted:
                certify(f'transport-{d}', term, wanted)
                emitted.add(d)
    print(f'{len(groups)} formal arrows; transported terms by dimension {dict(sorted(counts.items()))}.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    parser.add_argument('--terms', action='store_true', help='also check the cut-two formal arrows')
    parser.add_argument('--agda', type=Path, help='emit representative judgments from the term check')
    args = parser.parse_args()
    if min(args.m, args.n) < 1:
        parser.error('require positive globe dimensions')
    check(args.m, args.n)
    if args.terms or args.agda:
        if min(args.m, args.n) < 3:
            parser.error('the two-position term check needs both globe dimensions at least three')
        emitter = Emitter() if args.agda else None
        term_check(args.m, args.n, emitter)
        if emitter:
            args.agda.write_text(emitter.module(args.agda.stem, 'Transport entire diagonal homs by one formal arrow.'))
