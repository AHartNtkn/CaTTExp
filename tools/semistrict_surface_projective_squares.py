"""Test primary Steenrod operations on a stable cone over real projective space."""

from argparse import ArgumentParser
from math import comb


def parity(n, k):
    return 0 <= k <= n and comb(n, k) % 2


def extension_rows(length):
    """Each bit a-1 is the coefficient of the new cell in Sq^(top-a)(t^a)."""
    top = length + 1
    for a in range(1, top):
        for s in range(1, top - a):
            r = top - a - s
            if r >= 2 * s:
                continue
            # Sq^s on t^a is computed before reaching the new cell.
            row = parity(a, s) << (a + s - 1)
            base = parity(a, s) & parity(a + s, r)
            for j in range(r // 2 + 1):
                if parity(s - j - 1, r - 2 * j) and parity(a, j):
                    row ^= 1 << (a + j - 1)
                    base ^= parity(a + j, r + s - j)
            if base:
                raise AssertionError(f"Adem relation failed on t^{a} at ({r}, {s})")
            yield row


def allows_bottom_square(length):
    # A class with bottom reading one exists exactly when the linear form
    # selecting the first coordinate is outside the span of the relations.
    pivots = {}
    for row in extension_rows(length):
        while row:
            col = row.bit_length() - 1
            if col not in pivots:
                pivots[col] = row
                break
            row ^= pivots[col]
    return 0 not in pivots


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=64, metavar="L")
    limit = parser.parse_args().through
    if limit < 6:
        parser.error("choose L >= 6 to include a non-power of two")
    allowed = []
    for length in range(4, limit + 1, 2):
        possible = allows_bottom_square(length)
        if possible != (length.bit_count() == 1):
            raise AssertionError(f"unexpected Steenrod extension at L={length}")
        if possible:
            allowed.append(length)
    print(f"Checked even L from 4 to {limit}. Primary relations allow {allowed}.")


if __name__ == "__main__":
    main()
