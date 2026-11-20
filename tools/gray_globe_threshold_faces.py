"""Test threshold faces of a globe pair and both orders of each distant square."""
import argparse
from collections import Counter
from itertools import product
from pathlib import Path

from gray_globe_comparison import atom, boundary, face, globe
from gray_globe_cubical_corner import map_rows
from gray_globe_distant_columns import patch
from gray_globe_end_charts import span
from gray_globe_factorizations import hole_split, profile, truncate
from gray_globe_section import EMPTY_ROW, cells, row_map
from gray_globe_shift_faces import linear
from gray_path_wedge import compose


def image(g, p, threshold, side):
    (i, _), (j, y) = g
    if i < p:
        return (g,)
    sign = y ^ (p % 2) if j < threshold else side
    signed = ((p, sign), (j, y))
    if 1 <= j <= threshold:
        return signed, ((p + 1, 2), (j - 1, 1 ^ sign ^ (p % 2)))
    return (signed,)


def homotopy(g, p, threshold):
    (i, _), (j, y) = g
    return Counter({((p + 1, 2), (j, y)): 1}) if i == p and j >= threshold else Counter()


def collapse(cell, p):
    def project(g):
        (i, x), q = g
        if i <= p:
            return (i, 2 if i == p else x), q
    return row_map(cell, 0, project)


def check_basis(p, n):
    counts = Counter()
    for t in range(n + 1):
        for g in product(globe(p), globe(n)):
            (i, _), (j, y) = g
            diff = linear(homotopy(g, p, t), boundary)
            diff.update(linear(boundary(g), lambda h: homotopy(h, p, t)))
            delta = Counter(image(g, p, t, 1))
            delta.subtract(image(g, p, t, 0))
            assert diff == delta
            counts['homotopies'] += 1
            for side in (0, 1):
                def move(h):
                    return Counter(image(h, p, t, side))
                assert linear(move(g), boundary) == linear(boundary(g), move)
                actual = map_rows(atom(g), move)
                assert collapse(actual, p) == atom(g)
                counts['signed images'] += 1
                if i == p and j <= t:
                    tag = y ^ (p % 2) if j < t else side
                    assert actual == face(atom(((p + 1, 2), (j, y))), tag)
                    counts['native faces'] += 1
    return counts


def check_patch(m, n, k, exterior):
    p, t, d = m - 1, k - m, k - 1
    paths = patch(m, n, k, exterior)
    horizontal = [None, None]
    vertical = [None, None]
    for path in paths:
        left = right = 0
        for cell in path:
            if span(cell, k) == (m, m):
                vertical[left] = cell
                right += 1
            else:
                horizontal[right] = cell
                left += 1
        assert left == right == 1
    old = collapse(horizontal[0], p)
    assert old == collapse(horizontal[1], p)
    labels = {g for row in old for chain in row for g in chain}
    marked, = (g for g in labels if g[0][0] == p and g[1][0] >= t)
    assert marked[1][0] == t
    for side in (0, 1):
        assert map_rows(old, lambda g: image(g, p, t, side)) == horizontal[side]
    for end, edge in enumerate(vertical):
        state = truncate(old, d, end)
        assert collapse(edge, p) == state
        caps = [map_rows(state, lambda g: image(g, p, t, side)) for side in (0, 1)]
        assert tuple(face(edge, side) for side in (0, 1)) == tuple(caps)
        raised, = homotopy(marked, p, t)
        assert edge[-1] == ((raised,), (raised,))


def check_reconstruction(m, n):
    p = m - 1
    counts = Counter()
    for w in cells((m, n)) - {()}:
        ranks = profile(w)
        old = collapse(w, p)
        v = max((j for i, j in ranks if i == p), default=-1)
        u = max((j for i, j in ranks if i == m), default=-1)
        assert u <= v
        if v < 0:
            assert w == old
            counts['fixed'] += 1
        elif u < v:
            images = [map_rows(old, lambda g: image(g, p, u + 1, s)) for s in (0, 1)]
            assert images.count(w) == 1
            counts['sectors'] += 1
        else:
            d = p + u
            end = truncate(old, d, 1)
            caps = [map_rows(end, lambda g: image(g, p, u, s)) for s in (0, 1)]
            assert caps[0][:-1] == caps[1][:-1]
            marked, = (g for g in end[-1][0] if g[0][0] == p)
            raised, = homotopy(marked, p, u)
            edge = caps[0][:-1] + ((caps[0][-1][0], caps[1][-1][0]), ((raised,), (raised,)))
            if old == end:
                assert edge == w
            else:
                base = map_rows(old, lambda g: image(g, p, u, 0))
                assert compose(base, edge + (EMPTY_ROW,) * (len(base) - len(edge)), d) == w
            counts['crossings'] += 1
    return counts


def check_terms(n, emitter):
    from catt import comp2, infer, subst_tm, subst_ty, v
    from gray_globe_exterior_actions import certificate
    from gray_globe_pure_extension import check, extend, raise_argument
    from gray_globe_sector_terms import arrow, verify

    p, d = 2, 3
    source = verify(p, n, None)
    old, generators, terms = source
    for c in cells((p, n)) - {()} - terms.keys():
        if (p, 2) not in profile(c):
            (left, right), = hole_split(c, 1, 1)
            terms[c] = comp2(old, 0, terms[left], terms[right])
    ctx, names, chosen = extend(source, (p, n), 0, p + 1, None)

    sigma = [[], []]
    marked = {}
    for index, (g, ty) in enumerate(zip(generators, old, strict=True)):
        for side in (0, 1):
            term = chosen[map_rows(atom(g), lambda h: image(h, p, 1, side))]
            assert infer(ctx, term) == subst_ty(ty, sigma[side])
            sigma[side].append(term)
        if g[0][0] == p and g[1][0] == 1:
            h = ((p + 1, 2), g[1])
            names[h] = v(len(ctx))
            ctx += (arrow(ctx, sigma[0][index], sigma[1][index]),)
            marked[g] = (index, h)

    def vertical(z):
        g, = (g for g in z[-1][0] if g in marked)
        index, h = marked[g]
        x, y, r = v(index), v(len(old)), v(len(old) + 1)
        formal = old + (infer(old, x),)
        formal += (arrow(formal, x, y),)
        action = raise_argument(formal, terms[z], x, r)
        return subst_tm(action, (*sigma[0], sigma[1][index], names[h]))

    domain = {w for w in cells((p + 1, n)) if w and (p, 2) not in profile(w)}
    samples = {}
    for w in sorted(domain, key=lambda c: (len(c), c)):
        ranks = profile(w)
        if (p, 1) not in ranks or (p + 1, 0) not in ranks:
            continue
        c = collapse(w, p)
        if (p + 1, 1) not in ranks:
            side, = (s for s in (0, 1) if map_rows(c, lambda g: image(g, p, 1, s)) == w)
            term = subst_tm(terms[c], sigma[side])
        else:
            z = truncate(c, d, 1)
            change = vertical(z)
            term = change if c == z else comp2(ctx, d, subst_tm(terms[c], sigma[0]), change)
            if c != z:
                samples.setdefault(len(w) - 1, w)
        chosen[w] = term
    assert chosen.keys() == domain
    check((ctx, names, chosen))
    if emitter:
        certify = certificate(emitter, ctx)
        for degree, w in samples.items():
            certify(f'crossing-{degree}', chosen[w], arrow(ctx, *(chosen[face(w, s)] for s in (0, 1))))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bound', type=int)
    parser.add_argument('--terms', type=int, choices=(3, 4))
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.agda and not args.terms:
        parser.error('--agda requires --terms')
    if args.bound < 3:
        parser.error('choose a bound of at least three to include a distant square')
    counts = Counter()
    for p, n in product(range(1, args.bound + 1), repeat=2):
        counts.update(check_basis(p, n))
        for k in range(max(p, n) + 1, p + n - 1):
            for exterior in (0, 1):
                check_patch(p, n, k, exterior)
                counts['distant squares'] += 1
    print(dict(counts))
    size = min(5, args.bound)
    print(f'Full reconstruction in {size} by {size}: {dict(check_reconstruction(size, size))}')
    if args.terms:
        from emit_agda import Emitter
        emitter = Emitter() if args.agda else None
        check_terms(args.terms, emitter)
        if emitter:
            args.agda.write_text(emitter.module(args.agda.stem, 'Crossings over a polarized stationary site.'))
