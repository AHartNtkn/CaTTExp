"""Check the two based loop orders at a square with one directed cancellation."""
from argparse import ArgumentParser
from pathlib import Path

from catt import arr, comp2, disc_tree, infer, maximal_vars, src, tdim_tm, tgt, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head
from semistrict_surface_directed_power_queries import apply, square


def right_unit_at(ctx, term, expand):
    rank = tdim_tm(ctx, term)
    disc = tree_ctx(disc_tree(rank))
    var = v(maximal_vars(disc)[0])
    padded = comp2(disc, rank - 1, var, ident(disc, tgt(disc, var)))
    ends = (var, padded) if expand else (padded, var)
    return apply(ctx, (disc, head(disc, *ends)), [term])


def check_raw(emitter):
    ctx, crossing = square(2)
    right, left = src(ctx, crossing), tgt(ctx, crossing)
    insert = right_unit_at(ctx, left, True)
    erase = right_unit_at(ctx, right, False)
    name = v(len(ctx))
    ctx += (arr(infer(ctx, left), tgt(ctx, insert), src(ctx, erase)),)
    reverse = composite(ctx, 2, [insert, name, erase])
    emitter.check_type('fittedReverse', ctx, reverse, arr(infer(ctx, left), left, right))

    left_loop = comp2(ctx, 2, reverse, crossing)
    right_loop = comp2(ctx, 2, crossing, reverse)
    cancel = v(len(ctx))
    ctx += (arr(infer(ctx, left_loop), left_loop, ident(ctx, left)),)
    # The other loop traversed twice contains a cancellable pair in its middle.
    middle = comp2(ctx, 2, comp2(ctx, 2, crossing, cancel), reverse)
    finish = comp2(ctx, 2, right_unit_at(ctx, crossing, False), reverse)
    start = comp2(ctx, 2, comp2(ctx, 2, crossing, left_loop), reverse)
    step = comp2(ctx, 3, middle, finish)
    emitter.check_type('rightTwiceToOnce', ctx, step, arr(infer(ctx, right_loop), start, right_loop))
    assert infer(ctx, cancel) != arr(infer(ctx, right_loop), right_loop, ident(ctx, right))


def reachable(word):
    seen = {word}
    todo = [word]
    while todo:
        current = todo.pop()
        for i in range(len(current) - 1):
            if current[i:i + 2] == 'zc':
                reduced = current[:i] + current[i + 2:]
                if reduced not in seen:
                    seen.add(reduced)
                    todo.append(reduced)
    return seen


def check_loops():
    checks = 0
    for lap in ('zc', 'cz'):
        for start in range(11):
            actual = reachable(lap * start)
            for end in range(11):
                expected = end <= start and (lap == 'zc' or start == 0 or end > 0)
                assert (lap * end in actual) == expected
                checks += 1
    return checks


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    check_raw(emitter)
    checks = check_loops()
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('DirectedSquareReturn', __doc__)
        (args.agda_dir / 'DirectedSquareReturn.agda').write_text(
            module.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))
    print(f'Checked {checks} based loop comparisons and the raw cancellation at the opposite base.')


if __name__ == '__main__':
    main()
