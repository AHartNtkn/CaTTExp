"""Select a smallest collection of cyclic top groups separating a shell's order-p subgroup."""

from argparse import ArgumentParser
from itertools import combinations, product
from math import isqrt


def add_pivot(row, pivots, p):
    row = [x % p for x in row]
    for j in sorted(pivots):
        if row[j]:
            scale = row[j]
            row = [(x-scale*y) % p for x, y in zip(row, pivots[j], strict=True)]
    j = next((i for i, x in enumerate(row) if x), None)
    if j is None:
        return False
    unit = pow(row[j], -1, p)
    pivots[j] = [unit*x % p for x in row]
    return True


def top_targets(p, orders, shells):
    if p < 2 or any(p % k == 0 for k in range(2, isqrt(p)+1)):
        raise ValueError("supply a prime")
    if any(k < 0 for k in orders) or any(len(x) != len(orders) for x in shells):
        raise ValueError("use nonnegative cyclic orders and one coordinate per order")
    if any(p*x % k if k else x for v in shells for x, k in zip(v, orders)):
        raise ValueError("supply generators killed by the chosen prime")
    candidates = []
    for j, order in enumerate(orders):
        if not order or order % p:
            continue
        power = p
        level = 1
        while order % (p*power) == 0:
            power *= p
            level += 1
        row = [(v[j] % power) // (power//p) for v in shells]
        candidates.append((level, j, power, row))
    pivots = {}
    return [(j, power, row) for _, j, power, row in sorted(candidates)
            if add_pivot(row, pivots, p)]


def audit_characters():
    count = 0
    for p in (2, 3, 5):
        orders = [p, 2*p*p if p != 2 else p*p, p**3]
        for k in range(p):
            generators = [[1, k*(orders[1]//p), 0], [1, 0, orders[2]//p]]
            tests = top_targets(p, orders, generators)
            for level in (1, 2, 3):
                modulus = p**level
                possible = [[z for z in range(modulus) if order*z % modulus == 0] for order in orders]
                characters = list(product(*possible))
                for coeffs in product(range(p), repeat=2):
                    values = [sum(a*b for a, b in zip(coeffs, coord)) % order
                              for coord, order in zip(zip(*generators), orders)]
                    detected = any(sum(x*y for x, y in zip(values, char)) % modulus for char in characters)
                    selected = any(size <= modulus and sum(x*y for x, y in zip(coeffs, row)) % p
                                   for _, size, row in tests)
                    assert selected == detected
                    count += 1
    return count


def audit_shuffles(m):
    # In the additive simplicial K(A,m), each complementary pair of surjections
    # gives the same sum simplex in the two orders. Accumulate integral chain coefficients.
    full = (1 << (2*m)) - 1
    coefficients = {}
    for jumps in combinations(range(2*m), m):
        bits = sum(1 << j for j in jumps)
        pair = tuple(sorted((bits, full ^ bits)))
        inversions = sum(j-i for i, j in enumerate(jumps))
        coefficients[pair] = coefficients.get(pair, 0) + (-1)**inversions
    assert all(abs(x) == (0 if m % 2 else 2) for x in coefficients.values())
    return len(coefficients)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int)
    parser.add_argument("--orders", type=int, nargs="*")
    parser.add_argument("--shell", type=int, action="append", nargs="*", default=[])
    args = parser.parse_args()
    if args.prime is None and args.orders is None and not args.shell:
        print(f"Verified {audit_characters()} cutoff and shell readings by direct enumeration of cyclic characters.")
        print(f"Checked {sum(audit_shuffles(m) for m in range(2, 9)):,} complementary shuffle pairs in degrees 2 through 8.")
    elif args.prime is None or args.orders is None:
        parser.error("supply a prime, ambient cyclic orders and shell generators")
    else:
        try:
            tests = top_targets(args.prime, args.orders, args.shell)
        except ValueError as exc:
            parser.error(str(exc))
        print(f"Minimum cyclic top groups for simultaneous counit detection: {len(tests)}.")
        for j, size, row in tests:
            print(f"Project coordinate {j+1} modulo {size}; order-{args.prime} readings {row}.")
