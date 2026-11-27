"""Check exterior maps before and after pruning at a compound lower pole."""
from argparse import ArgumentParser
from pathlib import Path

from catt import (comp2, disc_tree, infer, maximal_vars, sub_from, subst_tm,
                  subst_ty, tree_ctx, v)
from semistrict_surface_insertion_cut import Assertions, standard, variables


def identity(ctx, term, dimension):
    disc = tree_ctx(disc_tree(dimension))
    label = sub_from(disc, ctx, {maximal_vars(disc)[0]: term})
    return subst_tm(standard(disc, dimension + 1), label)


def compound_pole(rank):
    middle = ((), ())
    for _ in range(rank - 3):
        middle = (middle,)
    return middle


def chart(rank, split_edge, stage):
    # The middle column is a top disc, its exposed pole, or the pole split
    # into two temporal factors. The last column retains a free top input.
    middle = disc_tree(rank - 1 - bool(stage))
    if stage == 2:
        middle = compound_pole(rank)
    return tree_ctx(((),) * (1 + split_edge) + (middle, disc_tree(rank - 1)))


def exterior(rank, start, end):
    first, last = chart(rank, *start), chart(rank, *end)
    slots = list(map(v, maximal_vars(last)))
    edges = slots[:1 + end[0]]
    if not start[0] and end[0]:
        edges = [comp2(last, 0, *edges)]
    middle = slots[1 + end[0]:-1]
    if start[1] < 2 and end[1] == 2:
        middle = [comp2(last, rank - 2, *middle)]
    if start[1] == 0 < end[1]:
        middle = [identity(last, middle[0], rank - 1)]
    return sub_from(first, last, dict(zip(maximal_vars(first),
                                          edges + middle + slots[-1:], strict=True)))


def check(rank, rice):
    first, last = chart(rank, False, 0), chart(rank, True, 2)
    original = standard(first, rank)
    direct = exterior(rank, (False, 0), (True, 2))
    readings = set()
    for split in (False, True):
        for stage in range(3):
            state = split, stage
            ctx = chart(rank, *state)
            before = exterior(rank, (False, 0), state)
            after = exterior(rank, state, (True, 2))
            assert tuple(subst_tm(term, after) for term in before) == direct
            head = ('coh', ctx, subst_ty(original[2], before), variables(ctx))
            reading = subst_tm(head, after)
            assert infer(last, reading) == subst_ty(original[2], direct)
            rice.equal(last, reading, subst_tm(original, direct), 'specialized chart heads')
            readings.add(reading)
    assert len(readings) == 6

    # Put the final port at an identity as well. Its column remains distinct
    # from the preceding two-factor pole, including in the transported type.
    target = tree_ctx(((), (), compound_pole(rank), disc_tree(rank - 2)))
    labels = list(map(v, maximal_vars(target)))
    labels[-1] = identity(target, labels[-1], rank - 1)
    drop = sub_from(last, target, dict(zip(maximal_vars(last), labels, strict=True)))
    for reading in readings:
        endo = subst_tm(reading, drop)
        pole = infer(target, endo)[2]
        rice.equal(target, endo, identity(target, pole, rank - 1), 'endo readouts')

    disc = tree_ctx(disc_tree(rank))
    tip = v(maximal_vars(disc)[0])
    whiskered = comp2(disc, 0, identity(disc, v(0), 0), tip)
    rice.equal(disc, whiskered, tip, 'disc readouts')
    print(f'Rank {rank}: six distinct charts agree on every original position.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('catt_strict', type=Path)
    args = parser.parse_args()
    rice = Assertions()
    for rank in (3, 4):
        check(rank, rice)
    rice.run(args.catt_strict.resolve())
