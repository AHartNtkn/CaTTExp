"""Check the CaTT terms that turn a constant-ended cylinder into a globular cell."""
import argparse
from functools import cache
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, disc_tree, glue_tree, infer, maximal_vars,
                  sub_from, subst_tm, tdim_tm, tree_ctx, v)
from canonical_gray_two_discs import strict_interpreter
from ct_suspension import build, ident
from emit_agda import Emitter


def coherent(G, tree, arguments, pair, reverse):
    P = tree_ctx(tree)
    variables = maximal_vars(P)
    a, b = pair(P, *(v(i) for i in variables))
    if reverse:
        a, b = b, a
    assert infer(P, a) == infer(P, b)
    term = ('coh', P, arr(infer(P, a), a, b), tuple(v(i) for i in range(len(P))))
    infer(P, term)
    return subst_tm(term, sub_from(P, G, dict(zip(variables, arguments))))


def whisk(G, cut, cell, partner, side):
    if side == 0:
        return comp2(G, cut, cell, partner)
    return comp2(G, cut, partner, cell)


def correction(G, cap_base, rail, side, reverse):
    """Compare the padded side with the raw filler in either direction.

    The forward direction contracts the padded side to the raw filler. The
    base of the cap identity can be any appropriately typed term.
    """
    degree = len(rail)
    current, proof = cap_base, None
    for cut, partner in enumerate(rail[:-1]):
        p, q = tdim_tm(G, current), tdim_tm(G, partner)

        def pair(P, a, b):
            if side:
                a, b = b, a
            return (whisk(P, cut, ident(P, a), b, side),
                    ident(P, whisk(P, cut, a, b, side)))

        tree = glue_tree(p, cut, q) if side == 0 else glue_tree(q, cut, p)
        args = (current, partner) if side == 0 else (partner, current)
        step = coherent(G, tree, args, pair, reverse)
        if proof is not None:
            earlier = whisk(G, cut, proof, partner, side)
            step = comp2(G, degree, step, earlier) if reverse else comp2(G, degree, earlier, step)
        proof, current = step, whisk(G, cut, current, partner, side)

    filler = rail[-1]

    def unitor(P, f):
        face = infer(P, f)[2 + side]
        return whisk(P, degree - 1, ident(P, face), f, side), f

    unit = coherent(G, disc_tree(degree), (filler,), unitor, reverse)
    if proof is None:
        return unit
    lifted = whisk(G, degree - 1, proof, filler, side)
    return comp2(G, degree, unit, lifted) if reverse else comp2(G, degree, lifted, unit)


@cache
def tower(G, base, height):
    return base if height == 0 else ident(G, tower(G, base, height - 1))


def padded_side(G, cap, rail, side):
    for cut, term in enumerate(rail):
        cap = whisk(G, cut, cap, term, side)
    return cap


def check_tile(level, emitter):
    """Compare the transfer declarations to the cylinder formula and lift degeneracy."""
    G = level.G
    labels = [None] * len(G)
    for (side, (_, d, label)), i in level.end.items():
        labels[i] = ((0, side), (d, {'-': 0, '+': 1, '*': 2}[label]))
    for (_, d, label), i in level.mix.items():
        labels[i] = ((1, 2), (d, {'-': 0, '+': 1, '*': 2}[label]))
    value = strict_interpreter(G, labels)
    for g, i in level.mix.items():
        d, filler = g[1], v(i)
        rails = [[v(level.mix[('g', j, sign)]) for j in range(d)] for sign in ('+', '-')]
        caps = [v(level.end[side, g]) for side in (0, 1)]
        pair = [padded_side(G, caps[s], rails[s], s) for s in (0, 1)]
        assert tuple(pair) == G[i][2:]
        for rail in rails:
            rail.append(filler)
        l, r = [correction(G, caps[s], rails[s], s, s == 1) for s in (0, 1)]
        higher = comp2(G, d + 1, l, r)
        a, b = [padded_side(G, ident(G, caps[s]), rails[s], s) for s in (0, 1)]
        wanted = arr(infer(G, a), a, b)
        assert infer(G, higher) == wanted
        assert value(higher) == value(filler) + (((), ()),)
        if emitter is not None and g[2] == '*':
            emitter.check_type(f'degeneracy-{d}', G, higher, wanted)


def check_moving_caps(level, max_degree, emitter):
    """Lift globular extensions of a 3-cylinder with arbitrary 2-dimensional caps."""
    G = level.G
    g = ('g', level.k, '*')
    caps = [v(level.end[s, g]) for s in (0, 1)]
    raw = v(level.mix[g])
    G += (infer(G, raw),)
    plain = [raw, v(len(G) - 1)]
    rails = [[v(level.mix[('g', j, sign)]) for j in range(level.k)] + [plain[s]]
             for s, sign in enumerate(('+', '-'))]
    for degree in range(level.k + 2, max_degree + 1):
        A = arr(infer(G, plain[0]), *plain)
        plain = [v(len(G)), v(len(G) + 1)]
        G += (A, A)
        lifted = plain[:]
        for cut in range(level.k + 1, degree):
            l, r = [correction(G, tower(G, caps[s], cut - level.k - 1),
                               rails[s][:cut], s, s == 1) for s in (0, 1)]
            lifted = [comp2(G, cut, comp2(G, cut, l, h), r) for h in lifted]
        a, b = [padded_side(G, tower(G, caps[s], degree - level.k - 1),
                            rails[s], s) for s in (0, 1)]
        expected = arr(infer(G, a), a, b)
        assert expected != A
        for s, t in enumerate(lifted):
            assert infer(G, t) == expected
            if emitter is not None:
                emitter.check_type(f'moving-{degree}-{s}', G, t, expected)
            rails[s].append(t)
        print(f'Degree {degree}: both lifts have the prescribed moving-cap cylinder type')


def run(max_degree, certificate):
    if max_degree < 2:
        raise ValueError('use degree at least 2 for the nontrivial boundary check')
    context = (STAR, STAR)
    rails = [[], []]
    normalized = [v(0), v(1)]
    emitter = Emitter() if certificate else None
    levels = build(max_degree - 1)
    for level in levels:
        check_tile(level, emitter)
    if len(levels) > 2:
        check_moving_caps(levels[2], max_degree, emitter)
    labels = [((0, 0),), ((0, 1),)]
    for degree in range(1, max_degree + 1):
        if degree == 1:
            raw_type = arr(STAR, v(0), v(1))
        else:
            caps = [tower(context, v(s), degree - 1) for s in (0, 1)]
            a, b = [padded_side(context, caps[s], rails[s], s) for s in (0, 1)]
            raw_type = arr(infer(context, a), a, b)
        expected = arr(infer(context, normalized[0]), *normalized)
        assert degree == 1 or expected != raw_type
        sides = [v(len(context)), v(len(context) + 1)]
        context += (raw_type, raw_type)
        check_ctx(context)
        labels.extend([((degree, 0),), ((degree, 1),)])
        value = strict_interpreter(context, labels)
        padded = sides[:]
        for cut in range(degree - 1, 0, -1):
            left, right = [correction(context, tower(context, v(s), cut - 1),
                                      rails[s][:cut], s, s == 0) for s in (0, 1)]
            padded = [comp2(context, cut, comp2(context, cut, left, h), right) for h in padded]
        for s, t in enumerate(padded):
            assert infer(context, t) == expected
            assert value(t) == value(sides[s])
            if emitter is not None:
                emitter.check_type(f'face-{degree}-{s}', context, t, expected)
            rails[s].append(sides[s])
        normalized = padded
        print(f'Degree {degree}: both normalized fillers have the prescribed literal faces')
    if emitter is not None:
        certificate.write_text(emitter.module(certificate.stem, 'Constant-ended cylinder normalization.'))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('degree', type=int)
    parser.add_argument('--agda', type=Path, help='also emit checks in a standalone Agda module')
    args = parser.parse_args()
    run(args.degree, args.agda)
