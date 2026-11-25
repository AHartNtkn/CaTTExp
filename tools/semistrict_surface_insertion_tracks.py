"""Compare raw tracks around nested and independent published insertion steps."""
from argparse import ArgumentParser
from pathlib import Path

from catt import (arr, comp2, glue_tree, infer, maximal_vars, sub_from, subst_tm,
                  subst_ty, tgt, tree_ctx, ucomp)
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_elementary_insertions import exterior, slots
from semistrict_surface_grid_tracks import temporal
from semistrict_surface_insertion_cut import variables


def insert(operation, tree, path, inner):
    """Reindex the actual bound type when creating the new coherence head."""
    joined, change = exterior(tree, path, inner)
    ctx = tree_ctx(joined)
    old = subst_tm(operation, change)
    new = ('coh', ctx, subst_ty(operation[2], change), variables(ctx))
    return joined, change, new, head(ctx, old, new)


def check_pair(ctx, first, second, name, emitter):
    assert first != second
    assert infer(ctx, first) == infer(ctx, second)
    for label, source, target in ((name, first, second), (name + 'Back', second, first)):
        comparison = head(ctx, source, target)
        expected = arr(infer(ctx, source), source, target)
        assert infer(ctx, comparison) == expected
        if emitter:
            emitter.check_type(label, ctx, comparison, expected)


def nested(rank, emitter):
    pair = glue_tree(rank, rank - 1, rank)
    path = min(slots(pair))
    op = ucomp(tree_ctx(pair))
    triple, _, three, first = insert(op, pair, path, pair)
    four, change, finish, second = insert(three, triple, path, pair)
    ctx = tree_ctx(four)
    outer_first = temporal(ctx, subst_tm(first, change), second)

    # Lift the change of the inner standard head through the outer binary head.
    # The two source expressions on the final tree genuinely differ at this slot.
    incl = sub_from(tree_ctx(triple), ctx, dict(zip(maximal_vars(tree_ctx(triple)),
                    (variables(ctx)[i] for i in maximal_vars(ctx)[:-1]), strict=True)))
    tail = variables(ctx)[maximal_vars(ctx)[-1]]
    carried = comp2(ctx, rank - 1, subst_tm(first, incl), tail)
    other_tree, _, other_finish, last = insert(op, pair, path, triple)
    assert four == other_tree and finish == other_finish
    assert infer(ctx, carried)[2] == infer(ctx, outer_first)[2]
    assert infer(ctx, carried)[3] == infer(ctx, last)[2]
    assert infer(ctx, carried)[2] != infer(ctx, carried)[3]
    check_pair(ctx, outer_first, temporal(ctx, carried, last), 'nested', emitter)


def distinct(rank, cut, emitter):
    tree = glue_tree(rank, cut, rank)
    pair = glue_tree(rank, rank - 1, rank)
    p = tree_ctx(tree)
    ty = infer(p, ucomp(p))
    source = ty[2]
    padded = temporal(p, source, identity(p, tgt(p, source)))
    op = ('coh', p, arr(ty[1], padded, ty[3]), variables(p))
    assert infer(p, op) != ty

    def route(left):
        index = 0 if left else -1
        three, _, middle, first = insert(op, tree, sorted(slots(tree))[index], pair)
        other = sorted(slots(three))[-1 if left else 0]
        four, change, finish, second = insert(middle, three, other, pair)
        return four, finish, temporal(tree_ctx(four), subst_tm(first, change), second)

    four, finish, left = route(True)
    other, other_finish, right = route(False)
    assert four == other and finish == other_finish
    check_pair(tree_ctx(four), left, right, 'distinctCut' + str(cut), emitter)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
    for rank in (3, 4):
        emitter = Emitter() if args.agda_dir else None
        nested(rank, emitter)
        for cut in range(rank):
            distinct(rank, cut, emitter)
        if emitter:
            name = 'InsertionTracks' + str(rank)
            (args.agda_dir / (name + '.agda')).write_text(emitter.module(name, __doc__))
    print('Checked both directions of 2 nested and 7 distinct-branch diamonds.')
