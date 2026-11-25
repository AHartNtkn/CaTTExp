"""Amalgamate compatible one-scalar braid tracks, preserving the common rod track."""

from argparse import ArgumentParser
from itertools import combinations, product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_gap_braids import observe


def inverse(path):
    return tuple((pos, -sign) for pos, sign in reversed(path))


def restrict_path(order, path, kept):
    current = list(order)
    moves = []
    for pos, sign in path:
        a, b = current[pos:pos+2]
        if a in kept and b in kept:
            moves.append((sum(i in kept for i in current[:pos]), sign))
        current[pos:pos+2] = b, a
    return tuple(moves)


def read(slots, names, path):
    return observe([slots[i] for i in names], range(len(names)), path)


def amalgamate(slots, rod_count, base, readers):
    """Basepoint order is rods followed by scalars. All inputs are named loops."""
    rods = tuple(range(rod_count))
    rod_signature = read(slots, rods, base)
    if rod_signature[0] != rods:
        raise ValueError('expected a loop of named rods')
    total = list(base)
    for s, path in enumerate(readers, rod_count):
        names = rods + (s,)
        if read(slots, names, path)[0] != tuple(range(len(names))):
            raise ValueError('expected a loop in each scalar coordinate')
        restriction = restrict_path(names, path, set(rods))
        if read(slots, rods, restriction) != rod_signature:
            raise ValueError('incompatible common rod track')
        # The other scalar coordinates see the rod-only kernel loop with their
        # own scalar stationary at the right, hence a section of a null loop.
        approach = tuple((i, 0) for i in range(s-1, rod_count-1, -1))
        total.extend(approach + inverse(base) + path + inverse(approach))
    return tuple(total)


def scalar_turn(slots, rods, s, r):
    """Push s once about r, passing the intervening rods and returning."""
    names = rods + (s,)
    at = list(names)
    route = []
    for pos in range(len(rods)-1, r, -1):
        q = at[pos]
        a, b = slots[q]
        gap = slots[s][0]
        route.append((pos, 1 if a < gap < b else 0))
        at[pos:pos+2] = s, q
    return tuple(route) + ((r, 1), (r, 1)) + inverse(route)


def audit(slots):
    k = next(i for i, (a, b) in enumerate(slots) if a == b)
    rods = tuple(range(k))
    scalars = range(k, len(slots))
    all_names = tuple(range(len(slots)))
    # Three rods share a wire, so these literal different base paths agree.
    half1 = ((0, 1), (1, 1), (0, 1))
    half2 = ((1, 1), (0, 1), (1, 1))
    base, alternate = half1*2, half2*2
    assert read(slots, rods, alternate) == read(slots, rods, base)
    choices = []
    for s in scalars:
        turns = [scalar_turn(slots, rods, s, r) for r, (a, b) in enumerate(slots[:k])
                 if a < slots[s][0] < b]
        words = [(), *turns]
        for u, v in combinations(turns, 2):
            words.append(u + v + inverse(u) + inverse(v))
        choices.append([alternate + w for w in words])
    count = 0
    for parts in product(*choices):
        total = amalgamate(slots, k, base, parts)
        assert read(slots, all_names, total)[0] == all_names
        for s, part in zip(scalars, parts):
            kept = rods + (s,)
            got = restrict_path(all_names, total, set(kept))
            assert read(slots, kept, got) == read(slots, kept, part)
        count += 1
    try:
        amalgamate(slots, k, base, [(), *[c[0] for c in choices[1:]]])
    except ValueError as err:
        assert 'incompatible' in str(err)
    else:
        raise AssertionError('accepted inconsistent rod tracks')
    print('positions', slots, 'compatible tuples reconstructed', count)


def check_directed_extension(output):
    ctx = (STAR, arr(STAR, v(0), v(0)))
    pole = identity(ctx, identity(ctx, v(0)))
    ctx += (arr(infer(ctx, pole), pole, pole),)
    scalar = comp2(ctx, 0, comp2(ctx, 0, v(1), v(2)), v(1))
    # Put the rod at the actual weak faces of the internal-gap whiskering.
    three_type = infer(ctx, scalar)
    ctx += (three_type,)
    pair = comp2(ctx, 2, scalar, scalar)
    four_type = arr(three_type, pair, v(3))
    ctx += (four_type,)*3
    ctx += (arr(four_type, v(4), v(5)), arr(four_type, v(5), v(6)))
    check_ctx(ctx)
    path = comp2(ctx, 4, v(7), v(8))
    goal = arr(four_type, v(4), v(6))
    assert infer(ctx, path) == goal
    if output:
        emitter = Emitter()
        emitter.check_type('twoDirectedSteps', ctx, path, goal)
        name = 'MixedGapExtension'
        (output / (name+'.agda')).write_text(emitter.module(name, __doc__))
    print('typed two-step 5-path between changes from two gap scalars to one rod')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    audit([(0, 3), (1, 4), (0, 4), (1, 1), (1, 1), (3, 3)])
    audit([(0, 3), (1, 4), (0, 4), (0, 0), (2, 2), (4, 4)])
    check_directed_extension(args.agda_dir)
