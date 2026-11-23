"""Check the one-occurrence tape construction for fixed old Gray judgments."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, disc_tree, glue_tree, infer, maximal_vars, src, tgt, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_scalar_cube import cube_terms, exchange


def check_language():
    # A deterministic machine scans parity, then returns to its input on success.
    # The first rule is the start supplied by the change of old face.
    rules = [('S', 'LE'), ('E0', '0E'), ('O0', '0O'), ('E1', '1O'), ('O1', '1E'),
             ('ER', 'KR'), ('0K', 'K0'), ('1K', 'K1'), ('LK', 'S')]
    accepted = rejected = steps = 0
    for length in range(10):
        for digits in product('01', repeat=length):
            start = 'S' + ''.join(digits) + 'R'
            word = start
            seen = set()
            while word not in seen:
                seen.add(word)
                moves = [word[:p] + after + word[p + len(before):]
                         for before, after in rules for p in range(len(word))
                         if word.startswith(before, p)]
                if not moves:
                    break
                assert len(moves) == 1
                word, = moves
                steps += 1
            returns = word == start
            assert returns == (digits.count('1') % 2 == 0)
            if returns:
                accepted += 1
            else:
                assert word.endswith('OR')
                rejected += 1
    return accepted, rejected, steps


def check_faces(em, k, base, u, v_end):
    m = k - 2
    b = tgt(base, u)
    pole = tgt(base, b)
    assert infer(base, u) == infer(base, v_end)
    h = v(len(base))
    ctx = base + (arr(infer(base, pole), pole, pole),)
    letter = arr(infer(ctx, h), h, h)
    start, scan, rewind, end = (v(len(ctx) + i) for i in range(4))
    ctx += (letter,) * 4
    scan_end = comp2(ctx, m, scan, end)
    rewind_end = comp2(ctx, m, rewind, end)

    def bar(t, w):
        return comp2(ctx, m, comp2(ctx, m - 1, t, h), comp2(ctx, m - 1, b, w))

    source, final = bar(u, start), bar(v_end, start)
    middle, later = bar(v_end, scan_end), bar(v_end, rewind_end)
    assert infer(ctx, source) == infer(ctx, final)
    launch, step, accept = (v(len(ctx) + i) for i in range(3))
    ctx += (arr(infer(ctx, source), source, middle),
            arr(letter, scan_end, rewind_end), arr(letter, rewind_end, start))
    check_ctx(ctx)
    second, third = bar(v_end, step), bar(v_end, accept)
    assert (src(ctx, second), tgt(ctx, second)) == (middle, later)
    assert (src(ctx, third), tgt(ctx, third)) == (later, final)
    proof = comp2(ctx, k - 1, comp2(ctx, k - 1, launch, second), third)
    em.check_type(f'return{k}', ctx, proof, arr(infer(ctx, source), source, final))
    suffix = comp2(ctx, m - 1, b, end)
    extended = comp2(ctx, m, proof, suffix)
    first, last = (comp2(ctx, m, t, suffix) for t in (source, final))
    em.check_type(f'suffix{k}', ctx, extended, arr(infer(ctx, first), first, last))


def typed_checks(directory):
    em = Emitter()
    pair = tree_ctx(glue_tree(2, 0, 2))
    square = exchange(pair, *map(v, maximal_vars(pair)))
    check_faces(em, 3, pair, tgt(pair, square), src(pair, square))
    point = (STAR,)
    unit = identity(point, v(0))
    scalar = point + (arr(infer(point, unit), unit, unit),)
    p, q, _ = cube_terms(scalar, v(1), v(1), v(1))
    check_faces(em, 4, scalar, q, p)
    # Exercise the higher-cut formulas on independently named parallel 4-cells.
    disc = tree_ctx(disc_tree(4))
    two = disc + (disc[-1],)
    check_faces(em, 5, two, v(len(disc) - 1), v(len(disc)))
    name = 'SingleTapeGray'
    module = em.module(name, __doc__).replace('open import CaTTExp.Pure\n',
                                               'open import CaTTExp.Gray.Pure\n')
    (directory / (name + '.agda')).write_text(module)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    print('Returns, nonreturns, directed steps:', *check_language())
    if args.agda_dir:
        typed_checks(args.agda_dir)
