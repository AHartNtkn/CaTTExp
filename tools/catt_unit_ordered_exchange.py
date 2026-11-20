"""Check exchange after changing one event, retaining a track inside each temporal order."""

from argparse import ArgumentParser
from pathlib import Path

from catt import (arr, chain_tree, comp2, disc_tree, glue_tree, infer, maximal_vars, src,
                  sub_from, subst_tm, tgt, tree_ctx, v)
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_chart_paths import two_triangles, unitor
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity


def temporal_words(ctx, first, second, spatial, temporal):
    def beside(left, right):
        return comp2(ctx, spatial, left, right)

    early = comp2(ctx, temporal, beside(first, src(ctx, second)), beside(tgt(ctx, first), second))
    late = comp2(ctx, temporal, beside(src(ctx, first), second), beside(first, tgt(ctx, second)))
    return early, late


def record_square(emitter, name, context, label, left, right, square):
    left, right, square = (subst_tm(t, label) for t in (left, right, square))
    assert left != right and infer(context, left) == infer(context, right)
    boundary = arr(infer(context, left), left, right)
    assert infer(context, square) == boundary
    emitter.check_typed(name, context, square)
    emitter.check_type(name, context, square, boundary)


def check_exchange(rank, context, atoms, emitter):
    spatial, temporal = rank - 2, rank - 1
    pair = tree_ctx(glue_tree(rank, spatial, rank))
    first, second = maximal_vars(pair)
    exchange = head(pair, *temporal_words(pair, v(first), v(second), spatial, temporal))

    moving = tree_ctx(glue_tree(rank + 1, spatial, rank))
    change, fixed = map(v, maximal_vars(moving))
    initial, final = src(moving, change), tgt(moving, change)

    def exchange_at(term):
        return subst_tm(exchange, sub_from(pair, moving, {first: term, second: fixed}))

    def beside(left, right):
        return comp2(moving, spatial, left, right)

    # Each side moves just one factor of its own two-step temporal word.
    early = comp2(moving, temporal, beside(change, src(moving, fixed)), beside(tgt(moving, initial), fixed))
    late = comp2(moving, temporal, beside(src(moving, initial), fixed), beside(change, tgt(moving, fixed)))
    left = comp2(moving, rank, exchange_at(initial), late)
    right = comp2(moving, rank, early, exchange_at(final))
    square = head(moving, left, right)

    disk = tree_ctx(disc_tree(rank))
    top, = maximal_vars(disk)
    atom = v(top)
    padded = comp2(disk, temporal, atom, identity(disk, tgt(disk, atom)))
    proper_change = subst_tm(head(disk, atom, padded), sub_from(disk, context, {top: atoms[0]}))
    label = sub_from(moving, context, dict(zip(maximal_vars(moving), (proper_change, atoms[1]))))
    record_square(emitter, f'orders-{rank}', context, label, left, right, square)


def check_lower_change(rank, context, atoms, emitter):
    spatial, temporal = rank - 2, rank - 1
    shape = (chain_tree(2), disc_tree(1))
    for _ in range(spatial):
        shape = (shape,)
    ctx = tree_ctx(shape)
    bridge, first, second = map(v, maximal_vars(ctx))

    def dot(x, y):
        return comp2(ctx, temporal, x, y)

    def beside(x, y):
        return comp2(ctx, spatial, x, y)

    def vertical(x, y):
        return comp2(ctx, rank, x, y)

    def instance(shape_ctx, term, values):
        label = sub_from(shape_ctx, ctx, dict(zip(maximal_vars(shape_ctx), values)))
        return subst_tm(term, label)

    pair = tree_ctx(glue_tree(rank, spatial, rank))
    pair_words = temporal_words(pair, *map(v, maximal_vars(pair)), spatial, temporal)
    swap, undo = head(pair, *pair_words), head(pair, *reversed(pair_words))

    triple = chain_tree(3)
    for _ in range(temporal):
        triple = (triple,)
    chain = tree_ctx(triple)
    x, y, z = map(v, maximal_vars(chain))
    assoc_left = comp2(chain, temporal, comp2(chain, temporal, x, y), z)
    assoc_right = comp2(chain, temporal, x, comp2(chain, temporal, y, z))
    assoc, unassoc = head(chain, assoc_left, assoc_right), head(chain, assoc_right, assoc_left)

    shape = (chain_tree(2), ())
    for _ in range(spatial):
        shape = (shape,)
    whisk = tree_ctx(shape)
    x, y, pole = map(v, maximal_vars(whisk))
    together = comp2(whisk, spatial, comp2(whisk, temporal, x, y), pole)
    separately = comp2(whisk, temporal, comp2(whisk, spatial, x, pole), comp2(whisk, spatial, y, pole))
    distribute = head(whisk, together, separately)

    source, target = src(ctx, second), tgt(ctx, second)
    bridge0, bridge1 = beside(bridge, source), beside(bridge, target)
    first0, first1 = beside(first, source), beside(first, target)
    second0 = beside(src(ctx, bridge), second)
    second1, second2 = beside(tgt(ctx, bridge), second), beside(tgt(ctx, first), second)
    early = vertical(dot(instance(whisk, distribute, (bridge, first, source)), second2),
                     instance(chain, assoc, (bridge0, first0, second2)))
    late = dot(second0, instance(whisk, distribute, (bridge, first, target)))
    late = vertical(late, instance(chain, unassoc, (second0, bridge1, first1)))
    late = vertical(late, dot(instance(pair, undo, (bridge, second)), first1))
    late = vertical(late, instance(chain, assoc, (bridge0, second1, first1)))
    left = vertical(instance(pair, swap, (dot(bridge, first), second)), late)
    right = vertical(early, dot(bridge0, instance(pair, swap, (first, second))))
    square = head(ctx, left, right)

    # Fold the split at a nontrivial lower writing. Only the first event's
    # source changes; the two external top generators remain independent.
    disk = tree_ctx(disc_tree(temporal))
    pole = v(len(disk) - 1)
    back = head(disk, tgt(disk, unitor(disk, pole)), pole)
    proper_bridge = subst_tm(back, sub_from(disk, context, {pole[1]: src(context, atoms[0])}))
    assert src(context, proper_bridge) != tgt(context, proper_bridge)
    label = sub_from(ctx, context, dict(zip(maximal_vars(ctx), (proper_bridge, *atoms))))
    record_square(emitter, f'lower-orders-{rank}', context, label, left, right, square)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    context, atoms = two_triangles()
    for rank in (2, 3, 4):
        check_exchange(rank, context, atoms, emitter)
        check_lower_change(rank, context, atoms, emitter)
        context, atoms = susp_ctx(context), [susp_tm(a) for a in atoms]
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Exchange with both ordered endpoints retained.'))
    print('Ordered endpoint squares verified in generator ranks 2, 3 and 4.')
