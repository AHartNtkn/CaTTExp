"""Check the split and both folds of a whiskered generator with composite faces."""
import argparse
from collections import Counter
from itertools import product
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, disc_tree, infer, maximal_vars, src,
                  sub_from, subst_tm, subst_ty, tgt, tree_ctx, v)
from ct_suspension import ident, susp_ctx
from emit_agda import Emitter
from gray_cube_six_poles import pack_cell
from gray_globe_comparison import atom, close_atoms, globe, strict_cells
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head, string_tree


def typed_map(domain, codomain, values):
    assert len(values) == len(domain)
    for i, (ty, term) in enumerate(zip(domain, values)):
        assert infer(codomain, term) == subst_ty(ty, values[:i])
    return values


def label(arity, context, values):
    slots = maximal_vars(arity)
    assert len(slots) == len(values)
    return sub_from(arity, context, dict(zip(slots, values)))


def check_rank(m, emitter):
    d, cut = m - 1, m - 2
    endpoints = [(0, 1), (1, 2), (2, 3), (3, 4), (1, 5), (5, 3)]
    base = (STAR,) * 6 + tuple(arr(STAR, v(i), v(j)) for i, j in endpoints)
    for _ in range(cut):
        base = susp_ctx(base)
    left, b, c, right, e, f = map(v, range(len(base) - 6, len(base)))
    a0, a1 = comp2(base, cut, b, c), comp2(base, cut, e, f)
    ty = infer(base, a0)
    assert ty == infer(base, a1)
    old = base + (arr(ty, a0, a1),)
    z = v(len(base))
    x, z0, z1 = map(v, range(len(base), len(base) + 3))
    split = base + (ty, arr(ty, a0, x), arr(ty, x, a1))
    check_ctx(old)
    check_ctx(split)
    fixed = tuple(map(v, range(len(base))))
    insert = typed_map(old, split, fixed + (comp2(split, d, z0, z1),))

    def frame(ctx, l, active, r):
        return comp2(ctx, cut, comp2(ctx, cut, l, active), r)

    # Both one-sided cells are promotions of the same cap writing with
    # just its middle maximal input changing. The split fixes its literal poles.
    cap = frame(split, left, x, right)
    first, second = (frame(split, left, t, right) for t in (z0, z1))
    assert tgt(split, first) == src(split, second) == cap
    assert src(split, first) == frame(old, left, a0, right)
    assert tgt(split, second) == frame(old, left, a1, right)
    assert top_counts(split, first) == Counter([z0[1]])
    assert top_counts(split, second) == Counter([z1[1]])
    for name, term in [('sourceHalf', first), ('targetHalf', second)]:
        emitter.check_type(name + str(m), split, term, infer(split, term))

    # A loop whose two tracks depend separately on the outside whiskers.
    spatial = tree_ctx(string_tree(cut, [d, m, d]))
    l, active, r = map(v, maximal_vars(spatial))
    u = frame(spatial, l, active, r)
    other = head(spatial, src(spatial, u), tgt(spatial, u))
    assert u != other
    loop = comp2(spatial, m, head(spatial, u, other), head(spatial, other, u))
    raw = subst_tm(loop, label(spatial, old, [left, z, right]))
    expanded = subst_tm(raw, insert)

    # Generic depth-one square with a free change of the marked input.
    upper = tree_ctx(string_tree(cut, [d, m + 1, d]))
    l, change, r = map(v, maximal_vars(upper))
    crossing = frame(upper, l, change, r)
    before, after = (subst_tm(loop, label(spatial, upper, [l, pole(upper, change), r]))
                     for pole in (src, tgt))
    square = head(upper, comp2(upper, m, before, crossing),
                  comp2(upper, m, crossing, after))

    # Two strict-identity inputs move on opposite sides of the active slot.
    # Their literal ends differ. Check the entire serial comparison on the
    # free three-slot arity before specializing the two idle inputs.
    three = tree_ctx(string_tree(cut, [m, m, m]))
    steps = list(map(v, maximal_vars(three)))
    initial = [src(three, step) for step in steps]
    final = [tgt(three, step) for step in steps]
    direct = head(three, frame(three, *initial), frame(three, *final))
    prefix = frame(three, steps[0], initial[1], initial[2])
    middle = frame(three, final[0], steps[1], initial[2])
    suffix = frame(three, final[0], final[1], steps[2])
    serial = comp2(three, d, comp2(three, d, prefix, middle), suffix)
    generic_comparison = head(three, direct, serial)
    low_disk = tree_ctx(disc_tree(d))
    top = v(len(low_disk) - 1)
    pad = comp2(low_disk, cut, top, ident(low_disk, tgt(low_disk, top)))
    idle = head(low_disk, top, pad)
    idle_left, idle_right = (subst_tm(idle, label(low_disk, old, [side]))
                             for side in (left, right))
    entries = label(three, old, [idle_left, z, idle_right])
    actual = subst_tm(generic_comparison, entries)
    upper_left = tgt(old, idle_left)
    marked_word = frame(split, upper_left, x, right)
    for pole, attachment in ((src, a0), (tgt, a1)):
        assert pole(old, subst_tm(middle, entries)) == subst_tm(marked_word, fixed + (attachment,))
    assert src(old, idle_left) != upper_left and src(old, idle_right) != tgt(old, idle_right)
    assert all(not top_counts(old, subst_tm(t, entries)) for t in (prefix, suffix))
    assert top_counts(old, subst_tm(middle, entries)) == Counter([z[1]])
    emitter.check_type('idleSlots' + str(m), old, actual,
                       arr(infer(old, subst_tm(direct, entries)), subst_tm(direct, entries),
                           subst_tm(serial, entries)))

    disk = tree_ctx(disc_tree(m))
    generator = v(len(disk) - 1)
    for at_source in (True, False):
        if at_source:
            fold_values = (a0, ident(old, a0), z)
            padded = comp2(disk, d, ident(disk, src(disk, generator)), generator)
        else:
            fold_values = (a1, z, ident(old, a1))
            padded = comp2(disk, d, generator, ident(disk, tgt(disk, generator)))
        fold = typed_map(split, old, fixed + fold_values)
        unitor = subst_tm(head(disk, generator, padded), label(disk, old, [z]))
        assert tgt(old, unitor) == subst_tm(insert[-1], fold) != z
        sigma = label(upper, old, [left, unitor, right])
        witness = subst_tm(square, sigma)
        bridge = frame(old, left, unitor, right)
        folded = subst_tm(expanded, fold)
        assert folded != raw
        start, end = comp2(old, m, raw, bridge), comp2(old, m, bridge, folded)
        expected = arr(infer(old, start), start, end)
        assert infer(old, witness) == expected
        name = ('sourceFold' if at_source else 'targetFold') + str(m)
        emitter.check_type(name, old, witness, expected)


def check_cube(n):
    m, d = n - 1, n - 2
    atoms = [pack_cell(atom(g)) for g in product(globe(1), repeat=n)
             if sum(dim for dim, _ in g) <= m]
    lower = [c for c in atoms if len(c) <= d + 1]
    actual = {pack_cell(c) for c in strict_cells((1,) * n, m) if len(c[-1][0]) == 1}
    recovered = set()
    marker = (-1, 0)
    for facet in (c for c in atoms if len(c) == m + 1):
        # Mark by a new d-atom at the literal strict lower poles of the facet.
        new_atom = facet[:d] + (((marker,), (marker,)),)
        words = close_atoms([*lower, new_atom], d)
        sources, targets = set(), set()
        for word in words:
            top = word[-1][0]
            if marker not in top:
                continue
            assert top.count(marker) == 1
            exterior = tuple(g for g in top if g != marker)
            sides = tuple(tuple(sorted(exterior + cap)) for cap in facet[-2])
            endpoints = [word[:-1] + ((s, s),) for s in sides]
            assert endpoints[0] not in sources and endpoints[1] not in targets
            sources.add(endpoints[0])
            targets.add(endpoints[1])
            cell = word[:-1] + (sides, facet[-1])
            assert cell in actual and cell not in recovered
            recovered.add(cell)
        assert sources.isdisjoint(targets)
    assert recovered == actual
    return len(actual)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    for rank in (3, 4, 5):
        check_rank(rank, emitter)
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Free-cap splitting and based loop transport.'))
    print('Checked both cap terms, both fold squares, and the two idle-slot changes in ranks 3–5.')
    for n in (3, 4, 5):
        print(f'{n}-cube: recovered all {check_cube(n)} single-facet cells from the independent marked closures.')
