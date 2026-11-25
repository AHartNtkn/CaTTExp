"""Compute binary relations on rank-two bottom squares for signed cell attachments."""

from argparse import ArgumentParser
from functools import cache
from itertools import product

from semistrict_surface_character_squares import admissible_form
from semistrict_surface_lens_squares import row_reduce


@cache
def admissible(total, maximum):
    if total == 0:
        return ((),)
    return tuple((a, *tail) for a in range(1, min(total, maximum) + 1)
                 for tail in admissible(total - a, a // 2))


@cache
def monomials(d, degree, minimum=()):
    """Polynomial basis in Serre's admissible generators of excess below d."""
    if degree == 0:
        return ((),)
    words = []
    for k in range(degree - d + 1):
        for generator in admissible(k, k):
            if generator < minimum or (generator and 2 * generator[0] - k >= d):
                continue
            for tail in monomials(d, degree - d - k, generator):
                words.append((generator, *tail))
    return tuple(words)


def unstable(d, word):
    """Evaluate one admissible word on the universal class of degree d."""
    multiplicity = 1
    while word:
        excess = 2 * word[0] - sum(word)
        if excess < d:
            break
        if excess > d:
            return None
        multiplicity *= 2
        word = word[1:]
    return (word,) * multiplicity


@cache
def square(d, k, word):
    if k == 0:
        return frozenset([word])
    if not word:
        return frozenset()
    if len(word) == 1:
        terms = set()
        for term in admissible_form((k, *word[0])):
            monomial = unstable(d, term)
            if monomial is not None:
                terms.symmetric_difference_update([monomial])
        return frozenset(terms)
    terms = set()
    for j in range(k + 1):
        for left, right in product(square(d, j, word[:1]), square(d, k-j, word[1:])):
            terms.symmetric_difference_update([tuple(sorted(left + right))])
    return frozenset(terms)


def reduce_vector(vector, pivots):
    for column in sorted(pivots, reverse=True):
        if vector & (1 << column):
            vector ^= pivots[column]
    return vector


def verify_characteristic(d):
    top = 2 * d + 2
    columns = {word: i for i, word in enumerate(monomials(d, top))}
    rows = (sum(1 << columns[t] for t in square(d, top - degree, word))
            for degree in range(d, top) for word in monomials(d, degree))
    pivots = row_reduce(rows)
    assert len(columns) - len(pivots) == 1
    assert reduce_vector(1 << columns[((), (2,))], pivots)
    return len(columns)


def parity_mask(row):
    return sum((value % 2) << i for i, value in enumerate(row))


def separate(vector, pivots):
    remainder = reduce_vector(vector, pivots)
    if not remainder:
        return None
    # Solve pivot equations from low to high with one selected free coordinate.
    character = remainder & -remainder
    for column in sorted(pivots):
        if (pivots[column] & character).bit_count() % 2:
            character |= 1 << column
    return character


def audit():
    for d in range(3, 32, 4):
        print(f"K(C2,{d}): {verify_characteristic(d)} top monomials, one independent reading")
    checked = 0
    for entries in product((-1, 0, 1), repeat=6):
        matrix = (entries[:3], entries[3:])
        first, second = map(parity_mask, matrix)
        span = {0, first, second, first ^ second}
        pivots = row_reduce((first, second))
        for vector in range(8):
            character = separate(vector, pivots)
            assert (character is None) == (vector in span)
            if character is not None:
                assert (character & vector).bit_count() % 2
                # Integer degrees of the extensions across the tester's doubled disk.
                for row in matrix:
                    degree = sum(v for j, v in enumerate(row) if (character >> j) & 1)
                    assert degree == 2 * (degree // 2)
            checked += 1
    print(f"Checked {checked} comparisons against direct signed-attachment relations.")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, help="local bottom d congruent to 3 modulo 4")
    parser.add_argument("--columns", type=int, help="number of bottom generators")
    parser.add_argument("--row", action="append", nargs="+", type=int, default=[])
    parser.add_argument("--shell", nargs="+", type=int, help="integer square coefficients")
    args = parser.parse_args()
    if args.degree is None and args.columns is None and not args.row and args.shell is None:
        audit()
        return
    if args.degree is None or args.degree < 3 or args.degree % 4 != 3:
        parser.error("choose a local degree d >= 3 congruent to 3 modulo 4")
    if args.columns is None or args.columns < 1:
        parser.error("supply a positive column count")
    if any(len(row) != args.columns for row in args.row):
        parser.error("every attaching row must have one entry per column")
    pivots = row_reduce(parity_mask(row) for row in args.row)
    print(f"Old comparison degree {2 * args.degree + 5}, exact kernel rank {args.columns - len(pivots)}.")
    if args.shell is not None:
        if len(args.shell) != args.columns:
            parser.error("supply one shell coefficient per column")
        char = separate(parity_mask(args.shell), pivots)
        if char is None:
            print("The raw difference is zero.")
        else:
            selected = [j + 1 for j in range(args.columns) if (char >> j) & 1]
            degrees = [sum(row[j - 1] for j in selected) // 2 for row in args.row]
            print(f"Nonzero raw difference. Fold columns {selected} to the single tester.")
            print(f"Degrees on its doubled attaching disk: {degrees}.")


if __name__ == "__main__":
    main()
