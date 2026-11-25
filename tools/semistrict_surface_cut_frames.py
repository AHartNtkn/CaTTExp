"""Check framed changes at a directed object cut and their generic comparisons."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import (
    STAR, arr, comp2, disc_tree, infer, maximal_vars, src, sub_from, subst_tm,
    tgt, tree_ctx, v,
)
from emit_agda import Emitter
from catt_unit_ordered_exchange import temporal_words
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity


def frame(ctx, left, term, right):
    return comp2(ctx, 0, comp2(ctx, 0, left, term), right)


def check_placements():
    # A and D both act on u:f=>g. No further u is composable there.
    # The only repair is at i[-]k. Generate its entire exterior closure.
    bound = 4
    reached = {('i', 'k')}
    pending = list(reached)
    while pending:
        left, right = pending.pop()
        additions = []
        if len(left) < bound:
            additions.extend((a + left, right) for a in 'ij')
        if len(right) < bound:
            additions.extend((left, right + b) for b in 'kh')
        for pair in additions:
            if pair not in reached:
                reached.add(pair)
                pending.append(pair)

    def words(alphabet):
        return [''.join(chars) for n in range(bound + 1) for chars in product(alphabet, repeat=n)]

    cases = list(product(words('ij'), words('kh')))
    assert reached == {(l, r) for l, r in cases if l.endswith('i') and r.startswith('k')}
    assert ('ji', 'kk') in reached and ('ij', 'kk') not in reached
    assert ('ji', 'kh') in reached and ('ji', 'hk') not in reached
    print(f'Checked {len(cases)} pairs of stationary paths, with {len(reached)} directed changes.')


def raw_changes(emitter):
    ctx = (STAR, STAR)
    x, y = v(0), v(1)
    ctx += (arr(STAR, x, x),) * 2 + (arr(STAR, y, y),) * 2
    i, j, k = v(2), v(3), v(4)
    ctx += (arr(STAR, x, y),) * 2
    f, g = v(6), v(7)
    ctx += (arr(infer(ctx, f), f, g),)
    u = v(8)
    ctx += (arr(infer(ctx, u), u, u),) * 2
    a, d = v(9), v(10)
    left, right = (frame(ctx, i, t, k) for t in (a, d))
    ctx += (arr(infer(ctx, left), left, right),)
    placed = frame(ctx, j, v(11), k)
    # Fit the nested boundary to an unbiased head on the same four wings.
    tree = ((), (), disc_tree(2), (), ())
    generic = tree_ctx(tree)
    slots = maximal_vars(generic)
    l0, l1, z, r1, r0 = map(v, slots)
    inner = frame(generic, l1, z, r1)
    nested = frame(generic, l0, inner, r0)
    start = frame(ctx, j, left, k)
    end = frame(ctx, j, right, k)
    assert (src(ctx, placed), tgt(ctx, placed)) == (start, end)
    unbiased = head(generic, src(generic, nested), tgt(generic, nested))
    assert unbiased != nested
    comparison = head(generic, unbiased, nested)
    reverse = head(generic, nested, unbiased)

    def specialize(term, moving):
        return subst_tm(term, sub_from(generic, ctx, dict(zip(slots, (j, i, moving, k, k)))))

    fitted = comp2(ctx, 3, comp2(ctx, 3, specialize(comparison, a), placed),
                   specialize(reverse, d))
    expected_start, expected_end = (specialize(unbiased, t) for t in (a, d))
    boundary = arr(infer(ctx, expected_start), expected_start, expected_end)
    assert infer(ctx, fitted) == boundary
    emitter.check_type('indexedChange', ctx, fitted, boundary)
    emitter.check_type('genericForward', generic, comparison, infer(generic, comparison))
    emitter.check_type('genericReturn', generic, reverse, infer(generic, reverse))

    # A stationary column of an outer interchanger can carry a nonliteral
    # 2-term on a whole path. Unfold its edge positions before relabelling.
    line = tree_ctx(((), ()))
    p, q = map(v, maximal_vars(line))
    pq = comp2(line, 0, p, q)
    unitor = head(line, comp2(line, 0, pq, identity(line, tgt(line, pq))), pq)
    chart = tree_ctx(((), (), disc_tree(1)))
    first, second, moving = maximal_vars(chart)
    line_sub = sub_from(line, chart, dict(zip(maximal_vars(line), (v(first), v(second)))))
    square = tree_ctx((disc_tree(1), disc_tree(1)))
    a_slot, b_slot = maximal_vars(square)
    early, late = temporal_words(square, v(a_slot), v(b_slot), 0, 1)
    labels = {a_slot: subst_tm(unitor, line_sub), b_slot: v(moving)}
    outer = subst_tm(head(square, late, early), sub_from(square, chart, labels))
    direct = head(chart, src(chart, outer), tgt(chart, outer))
    assert direct != outer
    fold = sub_from(chart, ctx, {first: i, second: i, moving: u})
    for label, s, t in (('unfoldWing', outer, direct), ('refoldWing', direct, outer)):
        cell = subst_tm(head(chart, s, t), fold)
        boundary = arr(infer(ctx, subst_tm(s, fold)), subst_tm(s, fold), subst_tm(t, fold))
        emitter.check_type(label, ctx, cell, boundary)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    check_placements()
    emitter = Emitter()
    raw_changes(emitter)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('CutFrames', __doc__).replace('open import CaTTExp.Pure',
                                                              'open import CaTTExp.Gray.Pure')
        (args.agda_dir / 'CutFrames.agda').write_text(module)
