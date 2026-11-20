"""Finite raw-syntax checks for canonical-gray-terms-r9, Researcher Response 1.

Use --agda FILE to emit the typed examples for the certified checker.
"""
import argparse
from functools import cache
from itertools import combinations_with_replacement
from pathlib import Path

from catt import (STAR, TypeError_, arr, chain_tree, check_ctx, check_ty_cached,
                  comp2, comp_tree, disc_tree, infer, maximal_vars, sub_from,
                  subst_tm, subst_ty, tdim_tm, tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from rc2 import path, struct_cell


def unary(context, term):
    disc = tree_ctx(disc_tree(tdim_tm(context, term)))
    top = len(disc) - 1
    return ('coh', disc, disc[top], sub_from(disc, context, {top: term}))


def write_bits(context, witness, bits, clock):
    degree = tdim_tm(context, witness)
    zero = ident(context, infer(context, witness)[3])
    one = unary(context, zero)
    args = [witness] + [one if bit else zero for bit in bits] + [zero] * (clock + 1)
    tree = chain_tree(len(args))
    for _ in range(degree - 1):
        tree = (tree,)
    return comp_tree(tree, context, args)


def vertex(index):
    return v(0 if index == 0 else 2 * index - 1)


def edge(start):
    return v(2 * start + 2)


@cache
def writing(size, start, end):
    context = tree_ctx(chain_tree(size))
    length = end - start
    if length == 0:
        return ident(context, vertex(start))
    if length == 1:
        return edge(start)
    witness = comp_tree(chain_tree(length), context, [edge(i) for i in range(start, end)])
    # On ordered interval supports the length determines the entire marked complex.
    # Use small clock values for the finite tests of encoding and exact replay.
    return write_bits(context, witness, [1] * length + [0], length)


def recognize_path(size, term):
    """Recognition on typed path terms with the small clocks used above."""
    context = tree_ctx(chain_tree(size))
    start_var, end_var = infer(context, term)[2:]
    vertices = {vertex(i): i for i in range(size + 1)}
    start, end = vertices[start_var], vertices[end_var]
    length = end - start
    if length < 2:
        return term == writing(size, start, end)
    if term[0] != 'coh' or term[1] != tree_ctx(chain_tree(2 * length + 3)):
        return False
    entries = [term[3][i] for i in maximal_vars(term[1])]
    zero = ident(context, end_var)
    one = unary(context, zero)
    raw = ucomp(tree_ctx(chain_tree(length)))
    renaming = [start_var]
    for i in range(start, end):
        renaming.extend((vertex(i + 1), edge(i)))
    return (entries[0] == subst_tm(raw, tuple(renaming))
            and entries[1:1 + length] == [one] * length
            and entries[1 + length:] == [zero] * (length + 2))


def path_maps(bound):
    tested = strict = 0
    for source in range(bound + 1):
        for target in range(bound + 1):
            context = tree_ctx(chain_tree(target))
            for f in combinations_with_replacement(range(target + 1), source + 1):
                substitution = [vertex(f[0])]
                for left, right in zip(f, f[1:]):
                    substitution.extend((vertex(right), writing(target, left, right)))
                equalities = []
                for left in range(source + 1):
                    for right in range(left, source + 1):
                        result = subst_tm(writing(source, left, right), substitution)
                        normal = writing(target, f[left], f[right])
                        assert path(context, result) == path(context, normal)
                        same = result == normal
                        assert recognize_path(target, result) == same
                        equalities.append(same)
                predicted = source < 2 or all(b == a + 1 for a, b in zip(f, f[1:]))
                assert all(equalities) == predicted, (source, target, f)
                strict += predicted
                tested += 1
    return tested, strict


def suspension_tests(emitter):
    for degree in range(1, 5):
        tree = chain_tree(2)
        for _ in range(degree - 1):
            tree = (tree,)
        context = tree_ctx(tree)
        witness = ucomp(context)
        term = write_bits(context, witness, [1, 0], 2)
        assert infer(context, term) == infer(context, witness)
        emitter.check_type(f'padding-{degree}', context, term, infer(context, witness))
        # Both alternative bit patterns and a different clock still have that type.
        for variant in (write_bits(context, witness, [0, 1], 2),
                        write_bits(context, witness, [1, 0], 3)):
            assert variant != term and infer(context, variant) == infer(context, witness)

    context = tree_ctx(chain_tree(2))
    raw = ucomp(context)
    for variant in (write_bits(context, raw, [0, 1, 1], 2),
                    write_bits(context, raw, [1, 1, 0], 3),
                    write_bits(context, unary(context, raw), [1, 1, 0], 2)):
        assert path(context, variant) == path(context, raw)
        assert not recognize_path(2, variant)


def square_collapse(emitter):
    # Vertices 00,10,01,11 and the two routes north-east and east-north.
    sides = ((0, 1), (2, 3), (0, 2), (1, 3))
    square = (STAR,) * 4 + tuple(arr(STAR, v(a), v(b)) for a, b in sides)
    north_east = comp2(square, 0, v(6), v(5))
    east_north = comp2(square, 0, v(4), v(7))
    poles = [write_bits(square, side, [1, 1, 0], 2) for side in (north_east, east_north)]
    declaration = arr(infer(square, poles[0]), *poles)
    check_ctx(square + (declaration,))

    target = tree_ctx(chain_tree(1))
    a, b, z = vertex(0), vertex(1), edge(0)
    sub = (a, a, b, b, ident(target, a), ident(target, b), z, z)
    left, right = (subst_tm(p, sub) for p in poles)
    assert left != right and path(target, left) == path(target, right) == path(target, z)
    square_type = subst_ty(declaration, sub)
    assert infer(target, ident(target, z)) != square_type
    lift = struct_cell(target, left, right)
    assert infer(target, lift) == square_type
    emitter.check_type('collapsed-square', target, lift, square_type)
    source_ctx = emitter.ctx(square + (declaration,))
    target_ctx = emitter.ctx(target)
    for label, top, expected in (('lifted', lift, 'true'),
                                 ('canonical', ident(target, z), 'false')):
        entries = emitter.sub(sub + (top,))
        emitter.checks.append(
            f'{label}-sub : is-just (checkSub {target_ctx} (from-just (checkCtx {target_ctx})) '
            f'{entries} {source_ctx}) ≡ {expected}\n{label}-sub = refl')

    side = struct_cell(target, left, z)
    back = struct_cell(target, z, left)
    cancellation = struct_cell(target, comp2(target, 1, side, back), ident(target, left))
    emitter.check_type('side', target, side, arr(infer(target, z), left, z))
    emitter.check_type('cancel', target, cancellation,
                       arr(infer(target, ident(target, left)),
                           comp2(target, 1, side, back), ident(target, left)))
    first, second = ident(target, left), ident(target, z)
    bare_arrow = arr(infer(target, first), first, second)
    bad_ctx = emitter.ctx(target + (bare_arrow,))
    emitter.checks.append(f'bare-arrow : is-just (checkCtx {bad_ctx}) ≡ false\nbare-arrow = refl')
    try:
        check_ty_cached(target, bare_arrow)
    except TypeError_:
        pass
    else:
        raise AssertionError('raw identity writings unexpectedly parallel')
    p, q = comp2(target, 1, first, side), comp2(target, 1, side, second)
    transported = struct_cell(target, p, q)
    emitter.check_type('identity-comparison', target, transported, arr(infer(target, p), p, q))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    suspension_tests(emitter)
    square_collapse(emitter)
    total, strict = path_maps(4)
    print(f'{total} path maps, {strict} strict. Padding, recognition and square collapse passed.')
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Canonical Gray terms, round 9.'))
