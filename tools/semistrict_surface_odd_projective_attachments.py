"""Compute the first detecting local comparison for odd projective attachments."""

from argparse import ArgumentParser
from itertools import product
from math import isqrt

from semistrict_surface_divisible_squares import diagonalize


def character(rows, shell, p):
    """Solve the homogeneous disk readings with normalized shell reading one."""
    size = len(shell)
    matrix = [[x % p for x in row] + [0] for row in rows]
    matrix.append([x % p for x in shell] + [1])
    pivots = []
    for col in range(size):
        k = len(pivots)
        pivot = next((i for i in range(k, len(matrix)) if matrix[i][col]), None)
        if pivot is None:
            continue
        matrix[k], matrix[pivot] = matrix[pivot], matrix[k]
        unit = pow(matrix[k][col], -1, p)
        matrix[k] = [unit * x % p for x in matrix[k]]
        for i, row in enumerate(matrix):
            if i != k and row[col]:
                matrix[i] = [(x - row[col]*y) % p for x, y in zip(row, matrix[k], strict=True)]
        pivots.append(col)
    if any(row[-1] for row in matrix[len(pivots):]):
        return None
    solution = [0]*size
    for i, col in enumerate(pivots):
        solution[col] = matrix[i][-1]
    return solution


def p_part(value, p):
    power = 1
    while value % (p*power) == 0:
        power *= p
    return power


def first_reading(rows, shell, upper_count, p):
    b = len(shell)
    matrix, columns, rank = diagonalize(rows, b, upper_count)
    divisors = [p_part(matrix[i][b+i], p) for i in range(rank)]
    for scale in sorted({1, *divisors}):
        constraints = [row[:b] for i, row in enumerate(matrix) if i >= rank or divisors[i] > scale]
        v = character(constraints, shell, p)
        if v is None:
            continue
        modulus = p*scale
        coordinates = [0]*upper_count
        for i, divisor in enumerate(divisors):
            if divisor <= scale:
                reading = sum(a*x for a, x in zip(matrix[i][:b], v, strict=True))
                unit = matrix[i][b+i] // divisor
                coordinates[i] = -(scale//divisor)*reading*pow(unit, -1, modulus//divisor) % (modulus//divisor)
        upper = [sum(a*x for a, x in zip(row, coordinates, strict=True)) % modulus for row in columns]
        values = [scale*x for x in v] + upper
        assert all(sum(a*x for a, x in zip(row, values, strict=True)) % modulus == 0 for row in rows)
        return modulus, v, upper
    return None


def audit():
    count = 0
    for p in (3, 5):
        shells = list(product(range(p), repeat=2))
        for d, e in product((-p*p, -1, 0, p), repeat=2):
            for bottom in (((1, 1), (1, -1)), ((1, 2), (-2, -4)), ((0, 1), (0, 0))):
                rows = [(*bottom[0], d), (*bottom[1], e)]
                expected = {}
                for scale in (1, p, p*p):
                    modulus = p*scale
                    for v in shells:
                        rhs = [scale*sum(a*x for a, x in zip(row, v, strict=True)) for row in bottom]
                        if any(all((r[-1]*y + z) % modulus == 0 for r, z in zip(rows, rhs, strict=True))
                               for y in range(modulus)):
                            for shell in shells:
                                if sum(a*x for a, x in zip(shell, v, strict=True)) % p:
                                    expected.setdefault(shell, modulus)
                for shell in shells:
                    result = first_reading(rows, shell, 1, p)
                    assert (result[0] if result else None) == expected.get(shell)
                    count += 1
        for height in range(6):
            scale = p**height
            rows = [(1, 0, scale, 2*scale), (0, 1, 3, 5), (1, 1, scale+3, 2*scale+5)]
            for shell in shells:
                result = first_reading(rows, shell, 2, p)
                expected = p if shell[1] else p*scale if shell[0] else None
                assert (result[0] if result else None) == expected
                count += 1
    print(f"Checked {count:,} marked shells against enumerated cyclic characters or explicit changes of basis.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int)
    parser.add_argument("--upper-count", type=int, default=0)
    parser.add_argument("--row", type=int, nargs="+", action="append", default=[])
    parser.add_argument("--shell", type=int, nargs="+")
    args = parser.parse_args()
    if args.prime is None and args.shell is None and not args.row and args.upper_count == 0:
        audit()
    elif (args.prime is None or args.prime < 3 or args.prime % 2 == 0
          or any(args.prime % k == 0 for k in range(3, isqrt(args.prime)+1, 2))):
        parser.error("supply an odd prime")
    elif not args.shell or args.upper_count < 0 or any(len(row) != len(args.shell)+args.upper_count for row in args.row):
        parser.error("supply the bottom shell, a nonnegative upper count and matching disk rows")
    else:
        result = first_reading(args.row, args.shell, args.upper_count, args.prime)
        if result:
            modulus, v, upper = result
            print(f"Least detecting cyclic order {modulus}. Projective degrees {v}. Upper sphere readings {upper}.")
        else:
            print("The marked bottom shell has a raw filler.")
