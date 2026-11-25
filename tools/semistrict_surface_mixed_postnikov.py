"""Compare degree-five classes on reversible presentations with free mixed generators."""

from argparse import ArgumentParser
from collections import Counter
from itertools import product

from catt import infer
from semistrict_surface_higher_winding import disk
from semistrict_surface_mixed_winding import Reading, evaluate, slots
from semistrict_surface_reversible_five import quotient


def compare(ranks, rows, face):
    """Coordinates: Hopf actions, mixed brackets in row-major order, upper spheres."""
    stationary, moving, upper = ranks
    size = moving + stationary * moving + upper
    if min(ranks) < 0 or any(len(v) != size for v in [*rows, face]):
        raise ValueError(f'expected nonnegative ranks and {size} entries per row and face')
    def reading(period):
        hopf = [[period * int(i == j) for j in range(size)] for i in range(moving)]
        return quotient([*rows, *hopf], face)
    return reading(2), reading(1)


def signed_disks():
    count = 0
    for rank, left in product((3, 4), (True, False)):
        ctx, term = disk(rank, left)
        first, at = slots(ctx)
        active, = (p for p in first if len(p) == rank)
        side = int(not left)
        for own, other, charge in product((-2, 0, 3), (-1, 0, 2), (-2, 0, 1)):
            intrinsic = Counter({(0, 0): own * charge - 5, (1, 1): 5})
            labels = [Reading(mass=own if p == active[:2] else other if len(p) == 2 else 0,
                              charge=charge if p == active else 0,
                              vertices=intrinsic if p == active else Counter()) for p in at]
            for vertex, face in zip(((1, side), (1, 1-side)), infer(ctx, term)[2:], strict=True):
                expected = intrinsic.copy()
                expected[vertex] += other * charge
                value = evaluate(face, labels, rank)
                assert value.vertices == expected and value.charge == charge
                assert value.vertices.total() == (own + other) * charge
            edges = evaluate(term, labels, rank).edges
            assert edges == Counter({((0, side), (1, side)): -other * charge,
                                     ((0, side), (1, 1-side)): other * charge})
            count += 1
    return count


def check_relations():
    # e is order two, w = e + k*y, and d*y = 0. Eliminate w independently.
    count = 0
    for k, d in product(range(-2, 3), (1, 2, 3, 4)):
        rows = [[1, -1, k], [0, 0, d]]
        for e, w, y in product(range(-2, 3), repeat=3):
            binary, joined = compare((1, 1, 1), rows, [e, w, y])
            assert (not any(joined)) == ((y + k*w) % d == 0)
            assert (not any(binary)) == ((y + k*w) % d == 0 and (e+w) % 2 == 0)
            count += 1
    return count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--ranks', type=int, nargs=3, metavar=('A', 'B', 'UPPER'))
    parser.add_argument('--row', action='append', type=int, nargs='*', default=[])
    parser.add_argument('--face', type=int, nargs='*')
    args = parser.parse_args()
    if args.ranks is None and args.face is None and not args.row:
        print(f'{signed_disks()} signed raw naturality disks and {check_relations()} quotient comparisons checked.')
    elif args.ranks is None or args.face is None:
        parser.error('provide --ranks and --face together')
    else:
        try:
            binary, joined = compare(args.ranks, args.row, args.face)
        except ValueError as error:
            parser.error(str(error))
        print(f'raw and individual binary fill: {not any(binary)}; joined fills: {not any(joined)}')
