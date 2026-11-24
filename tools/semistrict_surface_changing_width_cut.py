"""Check a cut with compound edges, nested expansions and directed inner comparisons."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import STAR, arr, comp2, disc_tree, infer, maximal_vars, src, sub_from, subst_tm, tgt, tree_ctx, v
from catt_unit_ordered_exchange import temporal_words
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_cut_frames import frame


def nested_changes(emitter):
    # Two loops live on opposite sides of the unique crossing edge.
    ctx = (STAR, STAR)
    x, y = v(0), v(1)
    ctx += (arr(STAR, x, x), arr(STAR, y, y), arr(STAR, x, y))
    i, k, f = v(2), v(3), v(4)
    expanded = frame(ctx, i, f, k)
    ctx += (arr(infer(ctx, f), f, expanded), arr(infer(ctx, f), expanded, f))
    up, down = v(5), v(6)
    nested_up, nested_down = (frame(ctx, i, t, k) for t in (up, down))
    first = comp2(ctx, 1, up, nested_up)
    last = comp2(ctx, 1, nested_down, down)
    assert tgt(ctx, first) == frame(ctx, i, expanded, k) == src(ctx, last)

    chart = tree_ctx(string_tree(1, [2, 2]))
    p, q = map(v, maximal_vars(chart))
    disk = tree_ctx(disc_tree(2))
    slot = maximal_vars(disk)[0]
    z = v(slot)
    changes = []
    for term, pad_right in ((p, True), (q, False)):
        padded = (comp2(disk, 1, z, identity(disk, tgt(disk, z))) if pad_right
                  else comp2(disk, 1, identity(disk, src(disk, z)), z))
        changes.append(subst_tm(head(disk, padded, z), sub_from(disk, chart, {slot: term})))
    early, late = temporal_words(chart, *changes, 1, 2)
    assert early != late
    sigma = sub_from(chart, ctx, dict(zip(maximal_vars(chart), (first, last))))
    for label, s, t in (('forwardSwitch', late, early), ('reverseSwitch', early, late)):
        proof = subst_tm(head(chart, s, t), sigma)
        boundary = arr(infer(ctx, subst_tm(s, sigma)), subst_tm(s, sigma), subst_tm(t, sigma))
        assert infer(ctx, proof) == boundary
        emitter.check_type(label, ctx, proof, boundary)

    # Nonidentity declared 3-change between the two-event excursion and the
    # empty history. Whisker it at the larger intermediate word.
    excursion = comp2(ctx, 1, up, down)
    empty = identity(ctx, f)
    ctx += (arr(infer(ctx, empty), empty, excursion),)
    placed = frame(ctx, i, v(7), k)
    emitter.check_type('placedExcursion', ctx, placed,
                       arr(infer(ctx, frame(ctx, i, empty, k)),
                           frame(ctx, i, empty, k), frame(ctx, i, excursion, k)))


def check_bounds(max_changes=5):
    # Insert the local excursion (+,-) in a gap of a path of positioned
    # 2-events. Stored entries are actual rules and their left/right frames.
    # Independently recognize the resulting words by their prefix heights.
    level = {()}
    for m in range(max_changes + 1):
        next_level = set()
        projected = set()
        for path in level:
            edge_word = 'f'
            projected.add(''.join(step for _, step, _ in path))
            for pos in range(len(path) + 1):
                left, right = edge_word.split('f')
                if m < max_changes:
                    inserted = ((left, '+', right), (left, '-', right))
                    next_level.add(path[:pos] + inserted + path[pos:])
                assert len(edge_word) <= 1 + 2 * len(path)
                if pos == len(path):
                    break
                a, change, b = path[pos]
                old, new = ('f', 'ifk') if change == '+' else ('ifk', 'f')
                assert edge_word == a + old + b
                edge_word = a + new + b
            assert edge_word == 'f'
        expected = set()
        for signs in product('+-', repeat=2 * m):
            height = 0
            for sign in signs:
                height += 1 if sign == '+' else -1
                if height < 0:
                    break
            else:
                if height == 0:
                    expected.add(''.join(signs))
        assert projected == expected and len(level) == len(expected)
        print(f'{m} inserted excursions: {len(level)} positioned 2-paths.')
        level = next_level


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    check_bounds()
    emitter = Emitter()
    nested_changes(emitter)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('ChangingWidthCut', __doc__).replace('open import CaTTExp.Pure',
                                                                    'open import CaTTExp.Gray.Pure')
        (args.agda_dir / 'ChangingWidthCut.agda').write_text(module)
