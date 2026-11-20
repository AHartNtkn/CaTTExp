"""Read cellular chains in a Benjamin–Markakis hom-computad from typed CaTT terms."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from pathlib import Path

from catt import (STAR, TypeError_, arr, comp2, disc_tree, infer, maximal_vars,
                  ps_dim, sub_from, subst_tm, tdim, tree_ctx, tree_of, v)
from ct_suspension import ident, susp_ctx, susp_tm, susp_ty
from emit_agda import Emitter
from gray_globe_branch_comparisons import cylinder
from partial_cylinder_steiner import trees
from relative_coherence_exchange_faces import head
from relative_coherence_point_joins import point_join


class OutsideSuspension(ValueError):
    pass


@cache
def strip_type(ty):
    if ty == arr(STAR, v(0), v(1)):
        return STAR
    if ty == STAR:
        raise OutsideSuspension
    return arr(strip_type(ty[1]), strip_term(ty[2]), strip_term(ty[3]))


@cache
def strip_term(term):
    if term[0] == 'v':
        if term[1] < 2:
            raise OutsideSuspension
        return v(term[1] - 2)
    _, chart, ty, labels = term
    small = strip_head(chart, ty)
    if small is None or labels[:2] != (v(0), v(1)):
        raise OutsideSuspension
    return ('coh', *small, tuple(map(strip_term, labels[2:])))


@cache
def strip_head(chart, ty):
    tree = tree_of(chart)
    if len(tree) != 1:
        return None
    small = tree_ctx(tree[0])
    try:
        sphere = strip_type(ty)
        generic = ('coh', small, sphere, tuple(map(v, range(len(small)))))
        infer(small, generic)
    except (OutsideSuspension, TypeError_):
        return None
    assert susp_ctx(small) == chart and susp_ty(sphere) == ty
    return small, sphere


@cache
def hom_chain(ctx, term):
    """Top occurrence vector. Keys are literal indecomposables, including hom objects."""
    degree = tdim(infer(ctx, term))
    if degree < 0:
        raise ValueError('a hom cell must have positive ambient dimension')
    if term[0] == 'v' or strip_head(term[1], term[2]) is None:
        return Counter({term: 1})
    counts = Counter()
    for ty, value in zip(term[1][2:], term[3][2:], strict=True):
        if tdim(ty) == degree:
            counts.update(hom_chain(ctx, value))
    return counts


def boundary(ctx, term):
    source, target = infer(ctx, term)[2:]
    counts = hom_chain(ctx, target).copy()
    counts.subtract(hom_chain(ctx, source))
    return {cell: n for cell, n in counts.items() if n}


def verify(output):
    checked = 0
    for size in range(7):
        for tree in trees(size):
            base = tree_ctx(tree)
            if ps_dim(base) > 3:
                continue
            join, cones = point_join(base)
            ctx = susp_ctx(join)
            for i, cone in enumerate(cones):
                result = Counter({susp_tm(v(i)): 1})
                if base[i] == STAR:
                    result[susp_tm(v(len(base)))] -= 1
                else:
                    result[susp_tm(cones[base[i][2][1]])] += 1
                    result[susp_tm(cones[base[i][3][1]])] -= 1
                assert boundary(ctx, susp_tm(cone)) == result
                checked += 1

    emitter = Emitter()
    for n in range(3):
        base = tree_ctx(disc_tree(n))
        ctx, _, mixed = cylinder(base, set(range(len(base))))
        cell = mixed[maximal_vars(base)[0]]
        for _ in range(2 - n):
            cell = ident(ctx, cell)
        chart = tree_ctx(((),) + disc_tree(3))
        arrow, globe = map(v, maximal_vars(chart))
        whiskered = comp2(chart, 0, arrow, globe)
        a = head(chart, whiskered, whiskered)
        b = ident(chart, whiskered)
        obj = infer(ctx, cell)
        while obj[1] != STAR:
            obj = obj[1]
        labels = sub_from(chart, ctx, {arrow[1]: ident(ctx, obj[2]), globe[1]: cell})
        first, second = (subst_tm(t, labels) for t in (a, b))
        assert hom_chain(ctx, first) == {first: 1} and not hom_chain(ctx, second)
        assert not boundary(ctx, first)
        for title, s, t, sign in [('down', a, b, -1), ('up', b, a, 1)]:
            witness = subst_tm(head(chart, s, t), labels)
            expected = arr(infer(ctx, first), subst_tm(s, labels), subst_tm(t, labels))
            assert infer(ctx, witness) == expected
            assert boundary(ctx, witness) == {first: sign}
            if output:
                emitter.check_type(title + str(n), ctx, witness, expected)
        power = second
        for k in range(8):
            assert hom_chain(ctx, power) == ({first: k} if k else {})
            power = comp2(ctx, 3, power, first)

    # Although the arity is a suspended point, its generic type uses a wrapped
    # arrow. Desuspending that wrapper would require a coherence of type star.
    line = tree_ctx(disc_tree(1))
    wrapped = head(line, v(0), v(1))
    state = ident(line, ident(line, wrapped))
    opaque = head(line, state, state)
    assert strip_head(line, infer(line, opaque)) is None
    assert hom_chain(line, opaque) == {opaque: 1}
    witness = head(line, opaque, ident(line, state))
    assert boundary(line, witness) == {opaque: -1}
    if output:
        emitter.check_type('genericSphere', line, witness, infer(line, witness))
        output.write_text(emitter.module(output.stem, 'Five-comparisons for hom-computad columns.'))
    print(f'{checked} suspended cone boundaries, three full cylinders, six directed '
          'columns, powers zero through seven, and one non-suspended generic sphere.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    verify(parser.parse_args().agda)
