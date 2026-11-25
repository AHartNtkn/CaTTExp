"""Compute the first unstable shell tests from bottom cyclic summands.

Order zero denotes an infinite cyclic summand. In odd bottom dimension
relations among the indicated squares can require higher attaching data.
"""
from argparse import ArgumentParser
from itertools import combinations, product
from math import gcd
from pathlib import Path


def tests(rank, bottom, orders):
    if rank < 2 or bottom <= rank or any(q < 0 or q == 1 for q in orders):
        raise ValueError('require 2 <= rank < bottom, with orders 0 or at least 2')
    candidates = []
    for j, q in enumerate(orders):
        if bottom % 2 == 0:
            if q and q % 2 == 0:
                candidates.append((j, q // 2))
        elif bottom not in (3, 7) and q % 2 == 0:
            if bottom in (15, 31, 63) and q % 4 == 2:
                # The odd multiple (q/2)x has order two and the same square.
                continue
            candidates.append((j, 1))
    return candidates


def tensor_reading(bottom, orders, coeffs):
    # Coordinates on brackets use one orientation per unordered pair.
    reading = [[0] * len(orders) for _ in orders]
    for (a, b), c in coeffs.items():
        reading[a][b] += c
        reading[b][a] += (-1) ** bottom * c
    for a, row in enumerate(reading):
        for b in range(len(row)):
            modulus = gcd(orders[a], orders[b])
            if modulus:
                row[b] %= modulus
    return reading


def product_square(m, left, right):
    """Integral Alexander–Whitney square on the shuffle product of two spheres."""
    value = 0
    for first_steps in combinations(range(2 * m), m):
        # Each oriented top simplex is a path with m steps in each factor.
        sign = (-1) ** sum(i - j for j, i in enumerate(first_steps))
        left_first = sum(i < m for i in first_steps)
        def evaluation(count):
            if count == m:
                return left
            if count == 0:
                return right
            return 0
        value += sign * evaluation(left_first) * evaluation(m - left_first)
    return value


def cyclic_maps():
    count = 0
    for source in (2, 4, 8, 16):
        for orders in ((2,), (4,), (8,), (2, 4), (4, 8), (6, 8), (8, 16)):
            choices = [[k for k in range(q) if source * k % q == 0] for q in orders]
            for image in product(*choices):
                for j, (q, k) in enumerate(zip(orders, image, strict=True)):
                    diagonal = source // 2 * k * k % q
                    exact_power = q & -q
                    expected = q // 2 if exact_power == source and k % 2 else 0
                    assert diagonal == expected
                    for t in range(j):
                        assert source * k * image[t] % gcd(q, orders[t]) == 0
                count += 1
    return count


def cyclic_attachments(directory):
    from catt import STAR, arr, comp2, infer, v
    from ct_suspension import ident
    from emit_agda import Emitter
    from semistrict_surface_shell_completion import round_trip_schema

    writer = Emitter()
    ctx = (STAR,)
    edge = ident(ctx, v(0))
    lower = ident(ctx, edge)
    blank = ident(ctx, lower)
    ctx += (arr(infer(ctx, lower), lower, lower),)
    loop = v(len(ctx))
    ctx += (arr(infer(ctx, blank), blank, blank),)
    unit = ident(ctx, blank)
    power = loop
    for q in range(2, 5):
        power = comp2(ctx, 3, power, loop)
        if q in (2, 4):
            assert infer(ctx, power) == infer(ctx, unit)
            presentation = writer.ctx(ctx + (arr(infer(ctx, unit), power, unit),))
            writer.checks.append(f'cyclic{q} : {presentation} ⊢ctx\n'
                                 f'cyclic{q} = from-just (checkCtx {presentation})\n')
    for rank in range(4, 10):
        round_trip_schema(rank, writer)
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'CyclicShells.agda').write_text(
        writer.module('CyclicShells', 'Cyclic attachments and their inverse schemas.'))


def audit():
    count = 0
    for m in (4, 5):
        for orders in ((2, 2), (2, 3), (3, 4), (4, 6), (2, 2, 3)):
            pairs = [(a, b) for a in range(len(orders)) for b in range(a, len(orders))]
            moduli = [gcd(orders[a], orders[b]) for a, b in pairs]
            if m % 2:
                moduli = [gcd(q, 2) if a == b else q
                          for q, (a, b) in zip(moduli, pairs, strict=True)]
            diagonals = tests(2, m, orders)
            predicted = set()
            for switches in product((0, 1), repeat=len(diagonals)):
                coefficients = {(j, j): c * s for (j, c), s in
                                zip(diagonals, switches, strict=True)}
                predicted.add(tuple(coefficients.get(pair, 0) for pair in pairs))
            for cs in product(*(range(q) for q in moduli)):
                reading = tensor_reading(m, orders, dict(zip(pairs, cs, strict=True)))
                assert (not any(any(row) for row in reading)) == (cs in predicted)
                count += 1
    assert tests(2, 3, (0, 2, 6)) == tests(6, 7, (0, 2, 6)) == []
    assert tests(3, 4, (0, 2, 3, 4, 6)) == [(1, 1), (3, 2), (4, 3)]
    assert tests(4, 5, (0, 2, 3, 4)) == [(0, 1), (1, 1), (3, 1)]
    for m in (15, 31, 63):
        assert tests(2, m, (0, 2, 4, 6, 9, 10)) == [(0, 1), (2, 1)]
    squares = 0
    for m in (3, 4, 5, 6):
        for q in (2, 4, 8):
            for c in (0, 1, q // 2, q):
                value = product_square(m, 1, c)
                assert value % (2 * q) == ((1 + (-1) ** m) * c) % (2 * q)
                if m % 2 == 0 and c == q // 2:
                    assert value % q == 0 and value % (2 * q) == q
                squares += 1
    print(f'Checked {count} tensor readings, {squares} integral cochain squares, '
          f'and {cyclic_maps()} cyclic-group homomorphisms.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--rank', type=int)
    parser.add_argument('--bottom', type=int)
    parser.add_argument('--orders', nargs='*', type=int, default=[])
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    if args.rank is None and args.bottom is None and not args.orders:
        audit()
    elif args.rank is None or args.bottom is None:
        parser.error('--rank and --bottom must be supplied together')
    else:
        basis = tests(args.rank, args.bottom, args.orders)
        print(f'Old filler degree {args.rank + 2 * args.bottom - 1}')
        for j, c in basis:
            print(f'{c} times the Whitehead square of bottom generator {j + 1}')
        degree_one_labels_detected = (
            args.bottom == args.rank + 1 and
            ((args.bottom + 1).bit_count() > 1 or
             all(args.orders[j] % 4 == 0 for j, _ in basis))
        )
        if args.bottom % 2 == 0 or not basis or degree_one_labels_detected:
            print(f'Exact kernel rank over F2: {len(basis)}')
        else:
            print('The indicated squares generate the kernel in the actual homotopy group.')
    if args.agda_dir:
        cyclic_attachments(args.agda_dir)
