"""Construct finite mixed-model coefficients for torsion-bottom Postnikov characters."""

from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import gcd, lcm


# A 5-simplex of K(C2,2) is a 2-cocycle on the ordered simplex.
# Each mask lists its values on triangles 0ij in lexicographic order.
FIVE_CYCLE = {7: 1, 8: -1, 25: 1, 43: 1, 50: 1, 144: 1, 162: 1}


def triangles(mask, order):
    values = {}
    for index, (i, j) in enumerate(combinations(range(1, 6), 2)):
        values[0, i, j] = (order // 2) * ((mask >> index) & 1)
    for i, j, k in combinations(range(1, 6), 3):
        values[i, j, k] = (values[0, j, k] - values[0, i, k] + values[0, i, j]) % order
    return values


def diagonal(order):
    """Push the integral cycle along C2 -> C_order and pair by Alexander-Whitney."""
    if order < 2 or order % 2:
        raise ValueError('the cycle needs an even cyclic order')
    boundary = Counter()
    total = 0
    for mask, weight in FIVE_CYCLE.items():
        values = triangles(mask, order)
        for skip in range(6):
            vertices = [i for i in range(6) if i != skip]
            face = tuple(values[vertices[0], j, k] for j, k in combinations(vertices[1:], 2))
            boundary[face] += (-1)**skip * weight
        coboundary = values[3, 4, 5] - values[2, 4, 5] + values[2, 3, 5] - values[2, 3, 4]
        assert coboundary % order == 0
        total += weight * values[0, 1, 2] * (coboundary // order)
    assert not any(boundary.values())
    return Fraction(total, order) % 1


def coefficients(orders, requested):
    """Rows are masses, columns are integral Bockstein charges."""
    if any(n < 2 for n in orders):
        raise ValueError('supply cyclic torsion orders at least two')
    slots = [(i, j) for i, n in enumerate(orders) for j in range(i, len(orders))
             if (i == j and n % 2 == 0) or (i != j and gcd(n, orders[j]) > 1)]
    if len(requested) != len(slots):
        raise ValueError(f'expected {len(slots)} coefficients for the slots {slots}')
    table = [[Fraction(0) for n in orders] for m in orders]
    values = []
    for (i, j), k in zip(slots, requested, strict=True):
        period = 2 if i == j else gcd(orders[i], orders[j])
        table[i][j] = Fraction(k % period, orders[i])
        values.append((i, j, Fraction(k, period) % 1))
    modulus = lcm(*(v.denominator for row in table for v in row))
    return modulus, [[int(modulus*v) for v in row] for row in table], values


def audit():
    for n in range(2, 65, 2):
        assert diagonal(n) == Fraction(1, 2)
    checks = 0
    for n in range(2, 15):
        for m in range(2, 15):
            g = gcd(n, m)
            # In the bottom tensor complex e2*f3 has boundary m*e2*f2
            # and e3*f2 has boundary n*e2*f2.
            assert (n//g)*m - (m//g)*n == 0
            size = int(n % 2 == 0) + int(g > 1) + int(m % 2 == 0)
            for k in range(-g, g+1):
                mod, table, values = coefficients([n, m], [k]*size)
                for i, j, expected in values:
                    ni = (n, m)[i]
                    unit = diagonal(ni) if i == j else Fraction(n//g, n)
                    assert (unit * ni * Fraction(table[i][j], mod)) % 1 == expected
                    assert (ni*table[i][j]) % mod == 0
                    checks += 1
    return checks


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int)
    parser.add_argument('--characters', nargs='*', type=int,
                        help='upper triangular order, skipping trivial summands')
    args = parser.parse_args()
    if args.orders is None and args.characters is None:
        print(f'Integral 5-cycle checked at 32 even orders; {audit()} finite coefficient readings checked.')
    elif args.orders is None or args.characters is None:
        parser.error('provide --orders and --characters together')
    else:
        try:
            modulus, table, values = coefficients(args.orders, args.characters)
        except ValueError as error:
            parser.error(str(error))
        print(f'Cyclic coefficient order {modulus}; mixed table {table}.')
        for i, j, value in values:
            print(f'({i+1}, {j+1}) reads {value} modulo one.')
