"""Decide rank-two square comparisons with signed attachments to upper spheres."""

from argparse import ArgumentParser
from itertools import product
from math import gcd

from semistrict_surface_framed_relations import parity_mask, separate
from semistrict_surface_lens_squares import row_reduce


def diagonalize(rows, b, c):
    """Row operations carry B along; column operations on D accumulate in V."""
    matrix = [list(r) for r in rows]
    columns = [[int(i == j) for j in range(c)] for i in range(c)]
    k = 0
    while k < min(len(matrix), c):
        nonzero = next(((i, j) for i in range(k, len(rows)) for j in range(k, c)
                        if matrix[i][b+j]), None)
        if nonzero is None:
            break
        i, j = nonzero
        matrix[i], matrix[k] = matrix[k], matrix[i]
        for row in matrix:
            row[b+j], row[b+k] = row[b+k], row[b+j]
        for row in columns:
            row[j], row[k] = row[k], row[j]
        while True:
            pivot = matrix[k][b+k]
            i = next((i for i in range(k+1, len(rows)) if matrix[i][b+k]), None)
            if i is not None:
                q = matrix[i][b+k] // pivot
                matrix[i] = [a - q*z for a, z in zip(matrix[i], matrix[k], strict=True)]
                if matrix[i][b+k]:
                    matrix[k], matrix[i] = matrix[i], matrix[k]
                continue
            j = next((j for j in range(k+1, c) if matrix[k][b+j]), None)
            if j is None:
                break
            q = matrix[k][b+j] // pivot
            swap = matrix[k][b+j] % pivot != 0
            for array, offset in ((matrix, b), (columns, 0)):
                for row in array:
                    row[offset+j] -= q * row[offset+k]
                    if swap:
                        row[offset+j], row[offset+k] = row[offset+k], row[offset+j]
        k += 1
    return matrix, columns, k


def valuation(value):
    return (value & -value).bit_length() - 1


def stable_stage(orders):
    # A free cyclic summand has divisible character group Q/Z.
    return 2 + max((valuation(order) for order in orders if order), default=0)


def solve(rows, b, c, shell):
    matrix, columns, rank = diagonalize(rows, b, c)
    pivots = row_reduce(parity_mask(row[:b]) for row in matrix[rank:])
    char = separate(shell, pivots)
    stage = max((valuation(matrix[i][b+i]) for i in range(rank)), default=0)
    if char is None:
        return b - len(pivots), stage, None
    half = 1 << stage

    def folded(row):
        return sum(x for j, x in enumerate(row[:b]) if char & (1 << j))

    z = [0] * c
    for i in range(rank):
        value = matrix[i][b+i]
        v = valuation(value)
        modulus = 2 * half >> v
        z[i] = ((half >> v) * folded(matrix[i]) * pow(value >> v, -1, modulus)) % modulus
    images = [sum(x*y for x, y in zip(row, z, strict=True)) for row in columns]
    disks = []
    for row in rows:
        total = sum(x*y for x, y in zip(row[b:], images, strict=True))
        degree, rem = divmod(total, half)
        double, odd = divmod(folded(row) - degree, 2)
        assert not rem and not odd
        disks.append((double, degree))
    return b - len(pivots), stage, (char, images, disks)


def audit():
    checked = 0
    for entries in product((-1, 0, 1), repeat=6):
        rows = [entries[:3], entries[3:]]
        x, y = (row[-1] for row in rows)
        g = gcd(x, y)
        if g:
            relations = [parity_mask([(y*rows[0][j] - x*rows[1][j]) // g for j in range(2)])]
        else:
            relations = [parity_mask(row[:2]) for row in rows]
        span = {0}
        for row in relations:
            span |= {v ^ row for v in span}
        for shell in range(4):
            rank, _, fold = solve(rows, 2, 1, shell)
            assert 1 << (2 - rank) == len(span)
            assert (fold is None) == (shell in span)
            checked += 1
    # Force both Euclidean row and column swaps with a unimodular change of upper basis.
    for a in range(9):
        for sign in (-1, 1):
            scale = sign * (1 << a)
            rows = [[1, 0, scale, 2*scale], [0, 1, 3, 5], [1, 1, scale+3, 2*scale+5]]
            for shell in range(4):
                rank, stage, fold = solve(rows, 2, 2, shell)
                assert (rank, stage) == (2, a) and (fold is None) == (shell == 0)
                checked += 1
        rank, stage, fold = solve([[1, 1 << a]], 1, 1, 1)
        assert (rank, stage) == (1, a) and fold is not None
        for k in range(a + 1):
            mod = 1 << (k + 1)
            assert any(((1 << a)*t - (1 << k)) % mod == 0 for t in range(mod)) == (k == a)
        for s in range(1, 12):
            mod = 1 << s
            image = {(1 << a)*t % mod for t in range(mod)}
            assert ((mod // 2) in image) == (s >= a + 1)
    print(f"Checked {checked} signed comparisons and the first allowable cellular folds through stage 8.")
    for order in range(2, 129):
        last = stable_stage([order]) - 1
        for initial in range(gcd(order, 2)):
            obstruction = initial
            for s in range(1, last):
                obstruction = (2 * obstruction) % gcd(order, 1 << (s + 1))
                if initial and s + 1 < last:
                    assert obstruction
            assert obstruction == 0
    for s in range(1, 10):
        modulus = 1 << min(s + 1, 3)
        doubles = {2 * x % modulus for x in range(modulus)}
        for lift in range(1 << min(s, 3)):
            assert 2 * lift % modulus in doubles
    print("Checked character obstructions on cyclic orders through 128 and the degree-11 bottom lifts.")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--bottom-count", type=int)
    parser.add_argument("--upper-count", type=int, default=0)
    parser.add_argument("--row", action="append", nargs="+", type=int, default=[])
    parser.add_argument("--shell", nargs="+", type=int)
    parser.add_argument("--stable-orders", nargs="+", type=int,
                        help="cyclic orders of reduced stable pi_7 of a degree-11 label (0 for Z)")
    args = parser.parse_args()
    b, c = args.bottom_count, args.upper_count
    if args.stable_orders is not None:
        if b is not None or c or args.row or args.shell or any(q < 0 for q in args.stable_orders):
            parser.error("supply the nonnegative stable orders independently of an attaching matrix")
        print(f"Universal degree-11 tester stage {stable_stage(args.stable_orders)} suffices.")
        return
    if b is None and not c and not args.row and args.shell is None:
        audit()
        return
    if b is None or b <= 0 or c < 0 or any(len(r) != b+c for r in args.row):
        parser.error("choose a positive bottom count, nonnegative upper count and matching rows")
    if args.shell is None or len(args.shell) != b:
        parser.error("supply one square coefficient per bottom generator")
    rank, stage, fold = solve(args.row, b, c, parity_mask(args.shell))
    print(f"Exact raw kernel rank {rank}, sufficient tester stage {stage}.")
    if fold is None:
        print("The raw difference is zero.")
    else:
        char, images, disks = fold
        print("Fold bottom columns", [j+1 for j in range(b) if char & (1 << j)])
        print("Upper sphere degrees", images)
        print("Degrees on the two tester disks", disks)


if __name__ == "__main__":
    main()
