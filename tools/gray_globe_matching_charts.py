"""Test the single-pasting-diagram criterion for faces of the globe-pair corner."""
import argparse
from functools import reduce
from itertools import product
from pathlib import Path

from canonical_gray_cube import build_cube
from canonical_gray_two_discs import cube_generators
from catt import infer, maximal_vars, src, sub_from, subst_tm, subst_ty, tgt, ucomp, v
from ct_suspension import susp_ty
from emit_agda import Emitter
from gray_globe_attachments import ordered_factors
from gray_globe_comparison import atom, face
from gray_globe_cubical_corner import cube_label, interval_image, map_rows, projected_chain
from gray_globe_exterior_actions import arity, certificate
from gray_globe_factorizations import rank
from gray_globe_section import EMPTY_ROW, trim
from gray_globe_strip_squares import lift_on
from gray_path_wedge import compose


def padded_composite(left, right, cut):
    height = max(len(left), len(right))
    return compose(left + (EMPTY_ROW,)*(height-len(left)),
                   right + (EMPTY_ROW,)*(height-len(right)), cut)


def matching_charts(m, n, h):
    k, offset = m+n-h, m-h
    poles = atom(((m, 2), (n, 2)))[:k]

    def rectangle(cell):
        return trim(poles + map_rows(cell, lambda g: projected_chain(m, n, h, g)))

    charts = instances = obstructions = 0
    for bits in product(range(3), repeat=h):
        moving = [i for i, x in enumerate(bits) if x == 2]
        if any(i+1 in moving for i in moving):
            obstructions += 1
            continue
        charts += 1
        source = [0 if x == 2 else x for x in bits]
        maximal = atom(cube_label(source))
        for i in moving:
            source[i] = 2
            edge = atom(cube_label(source))
            maximal = edge if len(maximal) == 1 else compose(maximal, edge, 0)
            source[i] = 1
        total = rectangle(maximal)
        owner = {}
        for row in total[k:]:
            for g in row[0]:
                i, j = rank(g)
                b = i-offset
                # Coordinate d (zero based) joins the sites d and d+1.
                owner[i, j] = b-1 if b-1 in moving else b
        slots = ordered_factors(total, k-1, owner)
        for choices in product(range(3), repeat=len(moving)):
            subface = list(bits)
            for idx, symbol in zip(moving, choices):
                subface[idx] = symbol
            values = []
            for slot in slots:
                if len(slot) == k+2:
                    i, _ = rank(slot[-1][0][0])
                    symbol = subface[i-offset-1]
                    if symbol != 2:
                        slot = face(slot, symbol)
                values.append(slot)
            actual = reduce(lambda a, b: padded_composite(a, b, k-1), values)
            assert actual == rectangle(atom(cube_label(subface)))
            instances += 1
    print(f'D^{m} tensor D^{n}, width {h}: {charts} matching charts, '
          f'{instances} signed face evaluations, {obstructions} faces containing a square obstruction.')


def adjacent_retractions(h):
    for start in range(h-1):
        for z in product(range(3), repeat=h):
            label = cube_label(z)
            small = cube_label(z[start:start+2])
            direct = () if 2 in z[:start]+z[start+2:] else (small,)
            if 2 not in z:
                image = (cube_label(interval_image(label)[0][start:start+2]),)
            else:
                image = ()
                for a, b, left, right in interval_image(label):
                    if start < a <= b <= start+2:
                        bits = [2, 2]
                        if a == start+2:
                            bits[0] = left
                        if b == start+1:
                            bits[1] = right
                        image = (cube_label(bits),)
            assert image == direct


def cube_substitution(emitter):
    # Once-suspended generic chart. Higher cuts are its globular suspensions.
    ambient = arity(0, (2, 2, 2))
    slots = tuple(map(v, maximal_vars(ambient)))
    sigma = [src(ambient, src(ambient, slots[0])), tgt(ambient, tgt(ambient, slots[-1]))]
    context, _ = build_cube()
    certify = certificate(emitter, ambient) if emitter else None
    for index, (g, ty) in enumerate(zip(cube_generators(), context, strict=True)):
        bits = tuple(x for _, x in g)
        args = tuple(slot if x == 2 else (src, tgt)[x](ambient, slot)
                     for slot, x in zip(slots, bits, strict=True))
        generic = arity(0, tuple(1 + (x == 2) for x in bits))
        wanted = subst_ty(susp_ty(ty), tuple(sigma))
        if bits.count(2) < 2:
            sub = sub_from(generic, ambient, dict(zip(maximal_vars(generic), args)))
            term = subst_tm(ucomp(generic), sub)
        else:
            term = lift_on(ambient, generic, args, *wanted[2:])
        assert infer(ambient, term) == wanted
        sigma.append(term)
        if certify:
            certify(f'face-{index}', term, wanted)
    print(f'{len(context)} suspended three-cube declarations instantiated at their exact types.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    parser.add_argument('h', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if not 1 <= args.h <= min(args.m, args.n):
        parser.error('require 1 <= h <= min(m,n)')
    matching_charts(args.m, args.n, args.h)
    adjacent_retractions(args.h)
    emitter = Emitter() if args.agda else None
    cube_substitution(emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Three separated changes in one spatial pasting context.'))
