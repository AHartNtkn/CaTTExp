"""Check the raw scalar cube boundaries and the orientation after folding its faces."""

from argparse import ArgumentParser
from collections import defaultdict
from itertools import permutations, product
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, glue_tree, infer, maximal_vars, src,
                  sub_from, subst_tm, tgt, tree_ctx, v)
from catt_unit_ordered_exchange import temporal_words
from emit_agda import Emitter
from gray_globe_comparison import atom
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_hom import cube_faces


def exchange(context, left, right):
    pair = tree_ctx(glue_tree(2, 0, 2))
    slots = maximal_vars(pair)
    early, late = temporal_words(pair, *map(v, slots), 0, 1)
    label = sub_from(pair, context, dict(zip(slots, (left, right))))
    return subst_tm(head(pair, late, early), label)


def cube_terms(context, left, middle, right):
    h = exchange(context, left, middle)
    u, v2 = src(context, h), tgt(context, h)
    hu = exchange(context, u, right)
    hv = exchange(context, v2, right)

    def cut(k, x, y):
        return comp2(context, k, x, y)

    early = cut(1, cut(0, h, src(context, right)), cut(0, tgt(context, u), right))
    late = cut(1, cut(0, src(context, u), right), cut(0, h, tgt(context, right)))
    p = cut(2, hu, early)
    q = cut(2, late, hv)
    boundary = arr(infer(context, src(context, hu)), src(context, hu), tgt(context, hv))
    assert p != q and infer(context, p) == infer(context, q) == boundary
    return p, q, boundary


def check_raw(emitter):
    point = (STAR,)
    unit = identity(point, v(0))
    context = (*point, arr(infer(point, unit), unit, unit))
    p, q, boundary = cube_terms(context, v(1), v(1), v(1))
    for name, term in [('outer-first', p), ('inner-first', q)]:
        emitter.check_type(name, context, term, boundary)

    # After conversion each mixed whisker of h is an iterated whisker
    # of an identity. Check both comparisons on each generic arity.
    for cut_dim, left_dim, right_dim, identity_on_left, name in [
            (0, 2, 1, True, 'spatial'), (1, 2, 2, True, 'prefix'),
            (1, 2, 2, False, 'suffix')]:
        ctx = tree_ctx(glue_tree(left_dim, cut_dim, right_dim))
        x, y = map(v, maximal_vars(ctx))
        combined = identity(ctx, comp2(ctx, cut_dim, x, y))
        split = (comp2(ctx, cut_dim, identity(ctx, x), y) if identity_on_left
                 else comp2(ctx, cut_dim, x, identity(ctx, y)))
        for label, s, t in [('contract', split, combined), ('expand', combined, split)]:
            emitter.check_type(name + '-' + label, ctx, head(ctx, s, t), arr(infer(ctx, s), s, t))
    disc = tree_ctx(disc_tree(2))
    x, = map(v, maximal_vars(disc))
    e = identity(disc, x)
    ee = comp2(disc, 2, e, e)
    for label, s, t in [('contract', ee, e), ('expand', e, ee)]:
        emitter.check_type('units-' + label, disc, head(disc, s, t), arr(infer(disc, s), s, t))


def check_cube():
    # P first moves 2 across the block [1,0], then orders the block.
    # Q first orders the block, then moves 2 past [0,1].
    def swaps(route):
        positions = []
        for old, new in zip(route, route[1:]):
            i, j = [k for k in range(3) if old[k] != new[k]]
            assert j == i + 1 and (old[i], old[j]) == (new[j], new[i])
            positions.append(i)
        return tuple(positions)

    p = swaps([(2, 1, 0), (1, 2, 0), (1, 0, 2), (0, 1, 2)])
    q = swaps([(2, 1, 0), (2, 0, 1), (0, 2, 1), (0, 1, 2)])
    assert atom(((1, 2),) * 3)[2] == (cube_faces(p), cube_faces(q))
    assert p.count(0) == q.count(0) + 1
    # Once the faces are folded, the crossing position is still a letter.
    # Check every admissible square on each of the six ordered paths.
    for order in permutations(range(3)):
        for k in range(2):
            if order[k] > order[k + 1]:
                changed = list(order)
                changed[k], changed[k + 1] = changed[k + 1], changed[k]
                assert swaps([order, changed]) == (k,)


def check_two_step_returns():
    """Compare directed reachability with the same-cut scalar criterion."""
    cases = 0
    for lengths in product(product(range(3), repeat=2), repeat=2):
        for width in range(6):
            graph = defaultdict(set)
            exchanges = []
            for left, right in product(range(2), repeat=2):
                s, t = lengths[left]
                u, v = lengths[right]
                for prefix in range(width - s - u + 1):
                    for gap in range(width - s - u - prefix + 1):
                        late = ((right, prefix + s + gap), (left, prefix))
                        early = ((left, prefix), (right, prefix + t + gap))
                        graph[late].add(early)
                        exchanges.append((late, early, (s, t, gap, u, v) == (0,) * 5))
            for late, early, expected in exchanges:
                seen = {early}
                pending = [early]
                while pending:
                    for neighbor in graph[pending.pop()] - seen:
                        seen.add(neighbor)
                        pending.append(neighbor)
                assert (late in seen) == expected
                cases += 1
    return cases


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path, help='emit checks for CaTTExp.Gray.Pure')
    args = parser.parse_args()
    emitter = Emitter()
    check_raw(emitter)
    check_cube()
    returns = check_two_step_returns()
    if args.agda:
        module = emitter.module(args.agda.stem, 'Directed scalar cube and identity comparisons.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n',
                                            'open import CaTTExp.Gray.Pure\n'))
    print('Parallel scalar terms, eight identity comparisons, and the directed cube 121 → 212 checked.')
    print(f'{returns:,} two-step exchange return tests checked by reachability.')
