"""Check Adem certificates and the degree-two character test for odd bottom squares."""

from argparse import ArgumentParser
from functools import cache

from semistrict_surface_lens_squares import row_reduce
from semistrict_surface_projective_squares import parity


def degree(j):
    return (1 << j) + 1


@cache
def monomials(total, first=0):
    """Nondecreasing lists of Serre generators of the indicated total degree."""
    if total == 0:
        return ((),)
    words = []
    j = first
    while degree(j) <= total:
        words.extend((j,) + tail for tail in monomials(total - degree(j), j))
        j += 1
    return tuple(words)


def generator_operations(j):
    yield 0, (j,)
    yield 1 << j, (j + 1,)
    if j >= 2:
        yield 1, (j - 1, j - 1)
    yield degree(j), (j, j)


@cache
def square(k, word):
    if not word:
        return frozenset({()}) if k == 0 else frozenset()
    terms = set()
    for shift, factor in generator_operations(word[0]):
        if shift <= k:
            for tail in square(k - shift, word[1:]):
                terms.symmetric_difference_update([tuple(sorted(factor + tail))])
    return frozenset(terms)


def vector(terms, columns):
    return sum(1 << columns[word] for word in terms)


def spherical_bound(stem):
    """Dimension of cohomology modulo positive Steenrod images in the stem."""
    columns = {word: i for i, word in enumerate(monomials(stem))}
    rows = (vector(square(stem - deg, word), columns) for deg in range(2, stem)
            for word in monomials(deg))
    return len(columns) - len(row_reduce(rows))


def primary_relations(top):
    """All new-cell readings of positive squares, related by every Adem pair."""
    words = [word for deg in range(2, top) for word in monomials(deg)]
    columns = {word: i for i, word in enumerate(words)}
    assert columns[(0,)] == 0
    for word in words:
        gap = top - sum(map(degree, word))
        for s in range(1, gap):
            r = gap - s
            if r >= 2 * s:
                continue
            lhs = square(s, word)
            row = vector(lhs, columns)
            base = set()
            for term in lhs:
                base.symmetric_difference_update(square(r, term))
            for j in range(r // 2 + 1):
                if parity(s - j - 1, r - 2 * j):
                    inner = square(j, word)
                    row ^= vector(inner, columns)
                    for term in inner:
                        base.symmetric_difference_update(square(gap - j, term))
            if base:
                raise AssertionError((word, r, s, base))
            yield row


@cache
def admissible_form(word):
    """Expand at the first inadmissible pair in the usual Steenrod basis."""
    for i, (a, b) in enumerate(zip(word, word[1:])):
        if a < 2 * b:
            terms = set()
            for j in range(a // 2 + 1):
                if parity(b - j - 1, a - 2*j):
                    middle = (a + b - j, j) if j else (a + b,)
                    terms.symmetric_difference_update(admissible_form(word[:i] + middle + word[i+2:]))
            return frozenset(terms)
    return frozenset([word])


def certificate(length):
    """Express Sq^L by positive outer squares with high-excess inner words."""
    r = length & -length
    if r == length or length < 2:
        raise ValueError("the length must have at least two binary digits set")
    base = length - r

    def expand(h, tail):
        a = h & -h
        b = base + h - a
        assert parity(b - 1, a)
        yield (a, b, *tail)
        for j in range(1, a // 2 + 1):
            if parity(b - j - 1, a - 2*j):
                yield from expand(h - j, (j, *tail))

    return tuple(expand(r, ()))


def check_certificate(length):
    terms = set()
    for word in certificate(length):
        assert sum(word) == length
        assert word[1] - sum(word[2:]) >= length - 2*(length & -length) + 1
        terms.symmetric_difference_update(admissible_form(word))
    assert terms == {(length,)}


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=64)
    parser.add_argument("--certificate", type=int, metavar="L")
    args = parser.parse_args()
    if args.certificate is not None:
        if args.certificate < 6 or args.certificate % 2 or args.certificate.bit_count() == 1:
            parser.error("choose an even non-power of two of at least six")
        check_certificate(args.certificate)
        for word in certificate(args.certificate):
            print(" ".join(f"Sq^{a}" for a in word))
        return
    if args.through < 6:
        parser.error("choose an upper length of at least six")
    lengths = range(6, args.through + 1, 2)
    for length in lengths:
        if length.bit_count() > 1:
            check_certificate(length)
    direct = []
    for length in lengths:
        allowed = 0 not in row_reduce(primary_relations(length + 2))
        if not spherical_bound(length + 1) and not allowed:
            direct.append(length)
    assert 6 in direct
    print(f"Verified the recursive Adem identities in admissible form through L={args.through}.")
    print("Lengths detected directly on K(C2,2) by both primary calculations:", direct)


if __name__ == "__main__":
    main()
