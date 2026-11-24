"""Check partial source lifts on empty attachments and the folded raw bubble."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import STAR, arr, comp2, infer, src, subst_tm, subst_ty, tgt, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity


def replay(row, move):
    # A row of H gates records its crossing port at every temporal seam.
    op, i = move
    p = row[i]
    if op == '+':
        m = 1 - p
        return row[:i + 1] + (m, p) + row[i + 1:], (op, p, m)
    m, q = row[i + 1:i + 3]
    if p != q:
        return None
    return row[:i + 1] + row[i + 3:], (op, p, m)


def moves(n):
    return [('+', i) for i in range(n + 1)] + [('-', i) for i in range(n - 1)]


def check_interchanges():
    yes = no = 0
    for n in range(5):
        for row in product((0, 1), repeat=n + 1):
            for cut in range(n + 1):
                for a, b in product(moves(cut), moves(n - cut)):
                    l, r = replay(row[:cut + 1], a), replay(row[cut:], b)
                    left_first = replay(row, a)
                    b_at_cut = (b[0], cut + b[1])
                    right_first = replay(row, b_at_cut)
                    lr = rl = None
                    if left_first:
                        delta = len(left_first[0]) - len(row)
                        lr = replay(left_first[0], (b[0], b_at_cut[1] + delta))
                    if right_first:
                        rl = replay(right_first[0], a)
                    if l and r:
                        expected = l[0] + r[0][1:]
                        assert lr == (expected, r[1]) and rl == (expected, l[1])
                        assert left_first[1] == l[1] and right_first[1] == r[1]
                        yes += 1
                    else:
                        assert lr is None and rl is None
                        no += 1
    print(f'{yes} defined interchange instances agree; both orders reject the other {no}.')


def build(emitter, coloured, all_births):
    ctx, fold = (), []

    def declare(ty, image):
        nonlocal ctx
        name = v(len(ctx))
        ctx += (ty,)
        fold.append(v(image))
        return name

    x = declare(STAR, 0)
    if coloured:
        y = declare(STAR, 0)
        ll = declare(arr(STAR, x, x), 1)
        f = declare(arr(STAR, x, y), 1)
        rr = declare(arr(STAR, y, y), 1)
        paths = (comp2(ctx, 0, f, rr), comp2(ctx, 0, ll, f))
    else:
        f = rr = declare(arr(STAR, x, x), 1)
        paths = (comp2(ctx, 0, f, f),)
    alpha = declare(arr(infer(ctx, f), f, f), 2)
    ports = range(len(paths))
    gates = {(p, q): declare(arr(infer(ctx, paths[p]), paths[p], paths[q]), 3)
             for p, q in product(ports, repeat=2)}
    rows = {(p, m): comp2(ctx, 1, gates[p, m], gates[m, p]) for p, m in product(ports, repeat=2)}
    empty = [identity(ctx, path) for path in paths]
    births = {(p, m): declare(arr(infer(ctx, empty[p]), empty[p], row), 4)
              for (p, m), row in rows.items() if all_births or not coloured or m != p}
    deaths = {(p, m): declare(arr(infer(ctx, row), row, empty[p]), 5)
              for (p, m), row in rows.items()}
    bubbles = {key: comp2(ctx, 2, birth, deaths[key]) for key, birth in births.items()}
    marked = comp2(ctx, 0, alpha, rr)
    pole = comp2(ctx, 1, marked, empty[0])
    selected = bubbles[0, int(coloured)]
    old_src, old_tgt = identity(ctx, pole), comp2(ctx, 1, marked, selected)
    change = declare(arr(infer(ctx, old_src), old_src, old_tgt), 6)
    padded = comp2(ctx, 3, identity(ctx, old_src), change)
    assert (src(ctx, padded), tgt(ctx, padded)) == (old_src, old_tgt)
    name = 'unmarked' if not coloured else 'bothChoices' if all_births else 'selected'
    emitter.check_type(name, ctx, padded, arr(infer(ctx, old_src), old_src, old_tgt))
    return ctx, tuple(fold), padded, bubbles


def raw_checks(emitter):
    base, _, original, plain = build(emitter, False, False)
    for both in (False, True):
        ctx, fold, lifted, bubbles = build(emitter, True, both)
        for i, ty in enumerate(ctx):
            assert subst_ty(ty, fold[:i]) == infer(base, fold[i])
        assert subst_tm(lifted, fold) == original
        emitter.check_eq('foldAll' if both else 'foldSelected', lifted, fold, original)
        if both:
            a, b = bubbles[0, 0], bubbles[0, 1]
            assert a != b and infer(ctx, a) == infer(ctx, b)
            for name, term in (('leftMid', a), ('rightMid', b)):
                assert subst_tm(term, fold) == plain[0, 0]
                emitter.check_eq(name, term, fold, plain[0, 0])


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    check_interchanges()
    emitter = Emitter()
    raw_checks(emitter)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('PartialLifts', __doc__).replace('open import CaTTExp.Pure',
                                                                  'open import CaTTExp.Gray.Pure')
        (args.agda_dir / 'PartialLifts.agda').write_text(module)
