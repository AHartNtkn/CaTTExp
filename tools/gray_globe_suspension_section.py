"""Split the first-axis desuspension map using the top atom of the right-hand cylinder."""
import argparse
from collections import Counter
from functools import cache
from itertools import product
from pathlib import Path

from canonical_gray_two_discs import strict_interpreter
from catt import comp2, infer, maximal_vars, src, subst_ty, tgt, v
from ct_suspension import susp_ty
from emit_agda import Emitter
from gray_globe_comparison import CORNERS, atom, face, globe
from gray_globe_corner_pullback import labelled_tableaux
from gray_globe_exterior_actions import arity, certificate
from gray_globe_factorizations import profile, rank, truncate
from gray_globe_section import EMPTY_ROW, omit, row_map
from gray_globe_sector_terms import edge_context, pure_type, tile
from gray_globe_strip_gluing import factors
from gray_globe_corner_prisms import fold
from gray_globe_strip_squares import chart_lift, minimal_shape


def opposite(label):
    degree, tag = label
    return degree, 1-tag if tag != 2 else 2


def erase(w):
    return row_map(w, 1, lambda g: ((g[0][0]-1, g[0][1]), opposite(g[1]))
                   if g[0][0] else None)


@cache
def cylinder_face(q, cap):
    """q is the (ordinary, untwisted) source projection label, cap is in the target."""
    degree, tag = q
    full = atom(((1, 2), cap))
    return full if degree == cap[0] else truncate(full, degree+1, tag)


def section(x, cap):
    # An input face globe uses ambient tags, including the total-opposite relabelling.
    projection = omit(x, 0, 0)
    (q,), = projection[-1][0]
    assert q[0] < cap[0] or q == opposite(cap)
    margin = cylinder_face(q, cap)
    rows = [margin[0]]
    for k, pair in enumerate(x, start=1):
        pure = margin[k] if k < len(margin) else EMPTY_ROW
        rows.append(tuple(tuple(sorted(
            [((p[0]+1, p[1]), opposite(s)) for p, s in chain] +
            [g for g in side if g[0][0] == 0])) for chain, side in zip(pair, pure)))
    return tuple(rows)


def projection_cap(x):
    (q,), = omit(x, 0, 0)[-1][0]
    return opposite(q)


def check(m, n):
    source = set(labelled_tableaux(m-1, n))
    target = {w for w in labelled_tableaux(m, n) if w[0] == CORNERS}
    cap = (n, 2)
    for x in source:
        w = section(x, cap)
        assert w in target and erase(w) == x
        if len(x) > 1:
            assert all(face(w, d) == section(face(x, d), cap) for d in (0, 1))
    for p in globe(m-1):
        g = (p, cap)
        assert section(atom(g), cap) == atom(((p[0]+1, p[1]), cap))

    cases = Counter()
    critical = [set(), set()]
    for w in target:
        x = erase(w)
        assert x in source
        q = projection_cap(x)
        s = q[0]
        height = max(b for _, b in profile(w))
        if s == height:
            assert s and w == section(x, q)
            cases['chosen face'] += 1
        else:
            if (1, s) not in profile(w):
                raise AssertionError('the desuspended projection was lost')
            if s == 0:
                pieces = factors(w, (1, 1))
                assert all(c == atom(c[-1][0][0]) for c in pieces)
                assert {rank(c[-1][0][0])[0] == 0 for c in pieces} == {False, True}
                cases['pure route'] += 1
                continue
            tight, pure = sorted(factors(w, (1, s+1)), key=lambda f: (0, s+1) in profile(f))
            assert tight == section(x, q)
            assert all(not r for r, t in profile(pure) if r+t > s)
            cases['with pure factor'] += 1
        if len(w) == 7 and len(w[-1][0]) == 1 and rank(w[-1][0][0]) == (3, 3):
            assert len(x) == 6 and len(x[-1][0]) == 1 and rank(x[-1][0][0]) == (2, 3)
            critical[s != height].add(minimal_shape(w))
    print(f'All {len(source)} cells of the smaller pair lifted; crossing cells: {dict(cases)}')
    if min(m, n) >= 5:
        assert tuple(map(len, critical)) == (33, 88) and not critical[0] & critical[1]
        interiors = {p for group in critical for w in group for p in profile(erase(w))
                     if p[0] >= 1 and p[1] >= 2}
        assert interiors == {(1, 2), (2, 2), (1, 3), (2, 3)}
        print('Single (3,3) shapes by direct lift or additional pure factor:', *map(len, critical))


def check_panels(m, n, emitter):
    """One substitution on all pure generators of the desuspended source."""
    ctx, names, _ = edge_context(m, n)
    evaluate = strict_interpreter(ctx, tuple(names))
    src_names, images = {}, {}
    # The two suspended poles are the extreme vertices.
    sigma = [names[corner[0]] for corner in CORNERS]
    expected_ctx = ()
    certified = set()
    certify = certificate(emitter, ctx) if emitter else None
    total = 0
    for g in sorted(product(globe(m-1), globe(n)), key=lambda g: sum(rank(g))):
        p, q = g
        if p[0] and q[0]:
            continue
        w = section(atom(g), (n, 2))
        if p[0] == 0:
            t = names[((1, p[1]), (n, 2))]
            for _ in range(n-q[0]):
                t = (src, tgt)[q[1]](ctx, t)
            kind = 'right'
        else:
            row = w[1][0]
            path = [next(h for h in row if atom(h)[0][0] == w[0][0])]
            path += [next(h for h in row if h != path[0])]
            left = names[w[-1][0][0]]
            edge, = (names[h] for h in path if not h[0][0])
            t = comp2(ctx, 0, edge, left) if not path[0][0][0] else comp2(ctx, 0, left, edge)
            kind = 'left'
        ty = pure_type(expected_ctx, src_names, g)
        wanted = subst_ty(susp_ty(ty), sigma)
        assert infer(ctx, t) == wanted and evaluate(t) == w
        if certify and (kind, q[1] if kind == 'left' else q[0]) not in certified:
            key = kind, q[1] if kind == 'left' else q[0]
            certify(f'{kind}-{key[1]}', t, wanted)
            certified.add(key)
        images[g] = t
        src_names[g] = v(len(expected_ctx))
        expected_ctx += (ty,)
        sigma.append(t)
        total += 1
    print(f'{total} suspended pure-panel variable images have their literal substituted types')
    if n > 1:
        check_edge_stacks(ctx, names, images, m, n, certify)


def paste_two_squares(ctx, wanted, squares):
    """Paste two adjacent 3-cells along their common 2-arrow in the hom."""
    def path(t):
        if t[0] == 'coh' and t[1] == arity(1, (2, 2)):
            return sum((path(t[3][i]) for i in maximal_vars(t[1])), ())
        return (t,)

    current, goal = wanted[2:]
    proof = []
    remaining = list(squares)
    while remaining:
        word = path(current)
        for t in remaining:
            before = path(src(ctx, t))
            hits = [i for i in range(len(word)-len(before)+1) if word[i:i+len(before)] == before]
            if hits:
                break
        else:
            raise AssertionError('no component square applies to the current path')
        i, = hits
        remaining.remove(t)
        for prefix in reversed(word[:i]):
            t = comp2(ctx, 1, prefix, t)
        for suffix in word[i+len(before):]:
            t = comp2(ctx, 1, t, suffix)
        if current != src(ctx, t):
            proof.append(chart_lift(ctx, word, 1, current, src(ctx, t)))
        proof.append(t)
        current = tgt(ctx, t)
    assert path(current) == path(goal)
    if current != goal:
        proof.append(chart_lift(ctx, path(goal), 1, current, goal))
    return fold(ctx, 2, proof)


def check_edge_stacks(ctx, names, panels, m, n, certify):
    """Type both cylinder inputs and check the common disk and the degree-zero stack."""
    old, labels, _ = tile(m-1, 0)
    evaluate = strict_interpreter(ctx, tuple(names))
    counts = Counter()
    for tag in (0, 1):
        edge = (1, 1-tag)
        change = names[((0, tag), (2, tag if n > 2 else 2))]
        middle, exterior = [], []
        for sigma in (middle, exterior):
            sigma.extend(names[z[0]] for z in CORNERS)
        pairs = {}
        for g, ty in zip(labels, old):
            p, q = g
            sp = p[0]+1, p[1]
            pure = names[(sp, (0, 1-tag))]
            def outside(t):
                return comp2(ctx, 0, pure, t) if tag else comp2(ctx, 0, t, pure)
            if q[0] == 0:
                u = names[(sp, (0, 1-q[1]))]
                f = names[((0, q[1]), edge)]
                core = comp2(ctx, 0, u, f) if q[1] else comp2(ctx, 0, f, u)
                ext = outside((src, tgt)[q[1]](ctx, change))
            else:
                core = names[(sp, edge)]
                if not p[0]:
                    ext = outside(change)
                else:
                    args = (pure, change) if tag else (change, pure)
                    src_ext, tgt_ext = subst_ty(susp_ty(ty), exterior)[2:]
                    ext = chart_lift(ctx, args, 0, src_ext, tgt_ext)
            for term, sigma in ((core, middle), (ext, exterior)):
                assert infer(ctx, term) == subst_ty(susp_ty(ty), sigma)
                sigma.append(term)
            pairs[g] = (ext, core) if tag == 0 else (core, ext)
            if q[0]:
                whole = section(atom((p, (1, tag))), (n, 2))
                assert evaluate(core) == atom((sp, edge))
                if not p[0]:
                    assert comp2(ctx, 1, *pairs[g]) == panels[(p, (1, tag))]
                else:
                    # The exterior mixed generator maps to a strict identity on
                    # the horizontal composite of the active disk and pure change.
                    assert evaluate(ext) == evaluate(outside(change)) + (EMPTY_ROW,)
                    assert whole[-1][0] == ((sp, edge),)
                counts[tag] += 1
                if certify and p == (m-1, 2):
                    certify(f'outer-{tag}', ext, infer(ctx, ext))
        # In hom dimension two spell out the stack, including all rebracketings.
        stacked = [names[z[0]] for z in CORNERS]
        for g, ty in zip(labels, old):
            p, q = g
            if p[0] > 1:
                stacked.append(None)
                continue
            wanted = subst_ty(susp_ty(ty), stacked)
            if p[0] and q[0]:
                term = paste_two_squares(ctx, wanted, pairs[g])
                assert evaluate(term) == section(atom((p, (1, tag))), (n, 2))
                if certify and p == (1, 2 if m == 2 else 0):
                    certify(f'stack-{tag}', term, wanted)
            else:
                source_label = (p, (1, tag)) if q[0] else g
                term = panels[source_label]
            assert infer(ctx, term) == wanted
            stacked.append(term)

        for p in globe(m-1):
            initial, seam = pairs[p, (0, 0)]
            other_seam, final = pairs[p, (0, 1)]
            assert seam == other_seam
            assert initial == panels[p, (0, 0)] and final == panels[p, (0, 1)]
    print('Both input cylinders checked on mixed generators by edge tag:', dict(counts))



if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.m < 2 or args.n < 1:
        parser.error('use m >= 2 and n >= 1')
    check(args.m, args.n)
    emitter = Emitter() if args.agda else None
    check_panels(args.m, args.n, emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Variable images on both pure panels.'))
