"""Check converted seams, their reversible repairs, and naturality on raised slots."""
from argparse import ArgumentParser
from collections import Counter
from pathlib import Path

from catt import (STAR, TypeError_, arr, check_ctx, comp2, disc_tree, glue_tree, infer, maximal_vars,
                  sub_from, subst_tm, tdim, tree_ctx, ucomp, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_full_binary import evaluate, generators, infer_surface, type_value
from semistrict_surface_identity_classes import marks, reflexive_pair, unary


def surface_comp(ctx, cut, left, right):
    """Keep the first spelling of a shared variable and check the other by conversion."""
    env = generators(ctx)
    ranks = [tdim(infer_surface(ctx, term)) + 1 for term in (left, right)]
    arity = tree_ctx(glue_tree(ranks[0], cut, ranks[1]))
    labels = dict(zip(maximal_vars(arity), (left, right)))
    for i in reversed(range(len(arity))):
        actual = infer_surface(ctx, labels[i])
        for slot, face in zip(arity[i][2:], actual[2:]):
            previous = labels.setdefault(slot[1], face)
            assert evaluate(previous, env) == evaluate(face, env)
    result = subst_tm(ucomp(arity), tuple(labels[i] for i in range(len(arity))))
    infer_surface(ctx, result)
    return result


def surface_head(ctx, start, end):
    ty = arr(infer_surface(ctx, start), start, end)
    result = ('coh', ctx, ty, tuple(map(v, range(len(ctx)))))
    assert infer_surface(ctx, result) == ty
    return result


def seam(point, rank, outside, pair, name, emitter):
    left, right = (unary(point, term) for term in pair)
    assert infer(point, left) == infer(point, right) == infer(point, outside)
    common = infer(point, outside)
    ctx = point + (arr(common, outside, left), arr(common, right, outside))
    check_ctx(ctx)
    a, b = v(len(point)), v(len(point) + 1)
    env = generators(ctx)
    assert left != right and evaluate(left, env) == evaluate(right, env)
    converted = surface_comp(ctx, rank, a, b)
    try:
        infer(ctx, converted)
    except TypeError_:
        pass
    else:
        raise AssertionError('the declared seam passed raw typing')
    assert type_value(ctx, infer_surface(ctx, converted)) == type_value(ctx, arr(common, outside, outside))
    imbalance = Counter(marks(ctx, left, rank))
    imbalance.subtract(marks(ctx, right, rank))
    assert any(imbalance.values()) and not marks(ctx, outside, rank)
    bridge = head(point, left, right)
    repaired = comp2(ctx, rank, comp2(ctx, rank, a, bridge), b)
    assert evaluate(repaired, env) != evaluate(converted, env)
    emitter.check_type(name + 'repair', ctx, repaired, arr(common, outside, outside))

    # Point operations supply the comparison and both cancellation cells.
    middle_unit = identity(point, left)
    forward = surface_head(point, bridge, middle_unit)
    backward = surface_head(point, middle_unit, bridge)
    for first, second, start in [(forward, backward, bridge), (backward, forward, middle_unit)]:
        round_trip = surface_comp(point, rank + 1, first, second)
        surface_head(point, round_trip, identity(point, start))
    # In the full surface the top units cancel, so these are the two actual
    # boundary comparisons between the repaired and the converted composites.
    for comparison, source, target in [(forward, repaired, converted), (backward, converted, repaired)]:
        lifted = surface_comp(ctx, rank, surface_comp(ctx, rank, a, comparison), b)
        expected = arr(arr(common, outside, outside), source, target)
        assert type_value(ctx, infer_surface(ctx, lifted)) == type_value(ctx, expected)


def naturality(rank, cut, emitter):
    # Two independently varying inputs. Compare a binary operation and its
    # unary-disc expansion before and after moving both inputs.
    tree = tree_ctx(glue_tree(rank, cut, rank))
    a, b = map(v, maximal_vars(tree))
    binary = comp2(tree, cut, a, b)
    expanded = unary(tree, binary)
    change = head(tree, expanded, binary)
    raised = tree_ctx(glue_tree(rank + 1, cut, rank + 1))
    x, y = map(v, maximal_vars(raised))
    def at(term, side):
        args = (infer(raised, z)[side] for z in (x, y))
        return subst_tm(term, sub_from(tree, raised, dict(zip(maximal_vars(tree), args))))
    def action(term):
        return head(raised, at(term, 2), at(term, 3))
    route1 = comp2(raised, rank, action(expanded), at(change, 3))
    route2 = comp2(raised, rank, at(change, 2), action(binary))
    assert route1 != route2
    ty = arr(infer(raised, route1), route1, route2)
    emitter.check_type(f'naturality{rank}cut{cut}', raised, head(raised, route1, route2), ty)
    emitter.check_type(f'reverse{rank}cut{cut}', raised, head(raised, route2, route1),
                       arr(ty[1], route2, route1))



def top_retraction(degree, emitter):
    # The newly adjoined filler and the existing one have the same two
    # literal faces. A second attachment enters at the padded face.
    disc = tree_ctx(disc_tree(degree - 1))
    z = v(len(disc) - 1)
    padded = comp2(disc, degree - 2, z, identity(disc, infer(disc, z)[3]))
    filler = head(disc, padded, z)
    y = v(len(disc))
    old = disc + (infer(disc, z), arr(infer(disc, z), y, padded))
    incoming = v(len(old) - 1)
    extended = old + (infer(disc, filler),)
    check_ctx(extended)
    paste = comp2(extended, degree - 1, incoming, v(len(old)))
    labels = tuple(map(v, range(len(old)))) + (filler,)
    projected = comp2(old, degree - 1, incoming, filler)
    assert subst_tm(paste, labels) == projected
    expected = arr(infer(old, z), y, z)
    emitter.check_type(f'extended{degree}', extended, paste, expected)
    emitter.check_type(f'projected{degree}', old, projected, expected)
    emitter.check_eq(f'retract{degree}', paste, labels, projected)
    source, target, assignment = emitter.ctx(old), emitter.ctx(extended), emitter.sub(labels)
    emitter.checks.append(
        f'sub{degree} : {source} ⊢sub {assignment} ∶ {target}\n'
        f'sub{degree} = from-just (checkSub {source} (from-just (checkCtx {source})) '
        f'{assignment} {target})\n')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    point = (STAR,)
    shared, ordinary = Emitter(), Emitter()
    lower = v(0)
    pairs = 0
    for rank in range(1, 4):
        z = identity(point, lower)
        square = comp2(point, rank - 1, z, z)
        families = {'unit': (square, z),
                    'assoc': (comp2(point, rank - 1, square, z), comp2(point, rank - 1, z, square))}
        if rank >= 2:
            families['reflexive'] = reflexive_pair(point, rank, lower)
        for family, pair in families.items():
            outside = identity(point, infer(point, pair[0])[2])
            seam(point, rank, outside, pair, family + str(rank), shared)
            pairs += 1
        for cut in range(rank):
            naturality(rank, cut, ordinary)
        lower = z
    for degree in (4, 5):
        top_retraction(degree, ordinary)
    if args.agda_dir:
        for name, emitter, kernel in [('OrdinarySeams', shared, 'Pure'), ('GraySeams', shared, 'Gray.Pure'),
                                       ('RaisedNaturality', ordinary, 'Pure')]:
            source = emitter.module(name, __doc__).replace('open import CaTTExp.Pure',
                                                          'open import CaTTExp.' + kernel)
            (args.agda_dir / (name + '.agda')).write_text(source)
    print(f'{pairs} converted seams, both repairs and cancellations; six naturality squares; two retractions over attachments.')


if __name__ == '__main__':
    main()
