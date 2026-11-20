"""Construct the two adjacent pure braid generators on three copies of a CaTT bubble."""
from argparse import ArgumentParser
from pathlib import Path

from catt import STAR, arr, comp2, disc_tree, glue_tree, infer, maximal_vars, src, sub_from, subst_tm, tgt, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_hom_chains import hom_chain


def compose(ctx, cut, *cells):
    result = cells[0]
    for cell in cells[1:]:
        result = comp2(ctx, cut, result, cell)
    return result


def pair_type(ctx, a, b):
    assert infer(ctx, a) == infer(ctx, b)
    return arr(infer(ctx, a), a, b)


def check_pair(ctx, forward, back, a, b):
    assert infer(ctx, forward) == pair_type(ctx, a, b)
    assert infer(ctx, back) == pair_type(ctx, b, a)


def unit_transport(ctx, bubble, left):
    disk = tree_ctx(disc_tree(2))
    z = v(len(disk)-1)
    line = tree_ctx(disc_tree(1))
    f = v(2)
    def pad(gamma, cell):
        if left:
            return comp2(gamma, 0, ident(gamma, v(0)), cell)
        return comp2(gamma, 0, cell, ident(gamma, v(1)))

    remove, insert = head(line, pad(line, f), f), head(line, f, pad(line, f))
    r = subst_tm(remove, sub_from(line, disk, {2: src(disk, z)}))
    l = subst_tm(insert, sub_from(line, disk, {2: tgt(disk, z)}))
    whiskered, aligned = pad(disk, z), compose(disk, 1, r, z, l)
    sigma = sub_from(disk, ctx, {z[1]: bubble})
    terms = [r, l, whiskered, aligned, head(disk, whiskered, aligned), head(disk, aligned, whiskered)]
    return [subst_tm(t, sigma) for t in terms]


def adjacent_crossings(ctx, bubble, emitter):
    r, l, b, a, b_to_a, a_to_b = unit_transport(ctx, bubble, False)
    other_r, other_l, d, other_a, d_to_other, other_to_d = unit_transport(ctx, bubble, True)
    # Both pairs of unitors live over the single point, although the two
    # specializations need not give the same writing for them.
    point = (STAR,)
    align = compose(ctx, 1, head(point, other_r, r), bubble, head(point, other_l, l))
    unalign = compose(ctx, 1, head(point, r, other_r), bubble, head(point, l, other_l))
    check_pair(ctx, align, unalign, other_a, a)
    d_to_a = comp2(ctx, 2, d_to_other, align)
    a_to_d = comp2(ctx, 2, unalign, other_to_d)
    check_pair(ctx, b_to_a, a_to_b, b, a)
    check_pair(ctx, d_to_a, a_to_d, d, a)

    chart = tree_ctx(glue_tree(2, 0, 2))
    x, y = (v(i) for i in maximal_vars(chart))
    xy = comp2(chart, 1, comp2(chart, 0, x, src(chart, y)), comp2(chart, 0, tgt(chart, x), y))
    yx = comp2(chart, 1, comp2(chart, 0, src(chart, x), y), comp2(chart, 0, x, tgt(chart, y)))
    sigma = sub_from(chart, ctx, {x[1]: bubble, y[1]: bubble})
    cross, uncross = (subst_tm(head(chart, s, t), sigma) for s,t in [(xy,yx),(yx,xy)])
    check_pair(ctx, cross, uncross, comp2(ctx, 1, b, d), comp2(ctx, 1, d, b))
    braid = compose(ctx, 2, comp2(ctx, 1, a_to_b, a_to_d), cross, comp2(ctx, 1, d_to_a, b_to_a))
    undo = compose(ctx, 2, comp2(ctx, 1, a_to_d, a_to_b), uncross, comp2(ctx, 1, b_to_a, d_to_a))
    doubled = comp2(ctx, 1, a, a)
    check_pair(ctx, braid, undo, doubled, doubled)

    chart = tree_ctx(string_tree(1, (2, 2, 2)))
    x, y, z = (v(i) for i in maximal_vars(chart))
    lhs, rhs = compose(chart, 1, x, y, z), comp2(chart, 1, x, comp2(chart, 1, y, z))
    sigma = sub_from(chart, ctx, {i: a for i in maximal_vars(chart)})
    assoc, unassoc = (subst_tm(head(chart,s,t),sigma) for s,t in [(lhs,rhs),(rhs,lhs)])
    triple = comp2(ctx, 1, doubled, a)
    left = [comp2(ctx, 1, t, a) for t in (braid, undo)]
    right = [compose(ctx, 2, assoc, comp2(ctx, 1, a, t), unassoc) for t in (braid, undo)]
    check_pair(ctx, *left, triple, triple)
    check_pair(ctx, *right, triple, triple)
    if emitter:
        for name, term in zip(('left', 'leftBack', 'right', 'rightBack'), left+right):
            emitter.check_type(name, ctx, term, pair_type(ctx, triple, triple))
    return triple, left[0], right[0]


def matrices():
    identity = (1, 0, 0, 1)
    left, right = (1, 1, 0, 1), (1, 0, -1, 1)
    def mul(a,b):
        x,y,z,w = a
        r,s,t,u = b
        return (x*r+y*t, x*s+y*u, z*r+w*t, z*s+w*u)
    assert mul(mul(left,right),left) == mul(mul(right,left),right)
    first, second = mul(left,left), mul(right,right)
    def inv(a):
        x,y,z,w = a
        return (w,-y,-z,x)
    actions = {-2: inv(second), -1: inv(first), 1: first, 2: second}
    seen = {identity}
    layer = [(0, identity)]
    for _ in range(7):
        layer = [(s, mul(m, actions[s])) for prev, m in layer for s in actions if s != -prev]
        keys = {m for _,m in layer}
        assert len(keys) == len(layer) and seen.isdisjoint(keys)
        seen.update(keys)
    return len(seen)


def run(emitter):
    point = (STAR,)
    unit = ident(point, v(0))
    ctx = point+(arr(infer(point,unit), unit, unit),)
    atom = v(1)
    for count in (1, 2, 3):
        bubble = compose(ctx, 1, *([atom]*count))
        triple, left, right = adjacent_crossings(ctx, bubble, emitter if count == 1 else None)
        x, y = comp2(ctx, 2, left, left), comp2(ctx, 2, right, right)
        u, w = comp2(ctx, 2, x, y), comp2(ctx, 2, y, x)
        assert u != w and infer(ctx, u) == infer(ctx, w) == pair_type(ctx, triple, triple)
        for power in (1, 2, 5):
            s, t = (compose(ctx, 2, *([value]*power)) for value in (u,w))
            for depth in range(3):
                assert hom_chain(ctx,s,depth) == hom_chain(ctx,t,depth)
            # One moving block, with a fixed braid and an inactive block of strands.
            padded = []
            for term in (s,t):
                framed = comp2(ctx, 2, left, term)
                framed = comp2(ctx, 1, framed, triple)
                padded.append(comp2(ctx, 0, unit, framed))
            assert infer(ctx, padded[0]) == infer(ctx, padded[1])
        if emitter and count == 1:
            for label, term in [('xy', u), ('yx', w)]:
                emitter.check_type(label, ctx, term, pair_type(ctx, triple, triple))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    run(emitter)
    print(f'Three bubble multiplicities, nine pairs of powers at all three depths; '
          f'{matrices()} distinct reduced-word matrices through length seven.')
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Adjacent bubble exchanges in both directions and the two anagrams.'))
