"""Compute width bounds for first-shell insertion tests on finite label CW complexes.

The audit computes the first two Adams Ext groups by the mod-two cobar
differential and checks a third-filtration differential target directly.
"""
from argparse import ArgumentParser
from functools import cache
from itertools import product

from semistrict_surface_lens_squares import row_reduce


def width_bound(length):
    if length < 6 or length % 2:
        raise ValueError('expected an even square degree of at least six')
    largest_power = 1 << (length.bit_length() - 1)
    if length != largest_power:
        return length - largest_power - 1, 2
    if length < 16:
        raise ValueError('the bottom square already vanishes on S^7')
    return 3 * length // 8, 4


@cache
def monomials(degree, index):
    if not index:
        return ((),) if not degree else ()
    weight = (1 << index) - 1
    return tuple(m + (s,) for s in range(degree // weight + 1)
                 for m in monomials(degree - s*weight, index - 1))


def add_monomials(x, y):
    return tuple(a+b for a, b in zip(x, y, strict=True))


@cache
def reduced_delta(m):
    zero = (0,) * len(m)
    terms = {(zero, zero)}
    for k, exp in enumerate(m, start=1):
        for bit in range(exp.bit_length()):
            if not exp & (1 << bit):
                continue
            summands = []
            for i in range(k + 1):
                left, right = list(zero), list(zero)
                if k > i:
                    left[k-i-1] = 1 << (bit+i)
                if i:
                    right[i-1] = 1 << bit
                summands.append((left, right))
            values = set()
            for a, b in terms:
                for x, y in summands:
                    values.symmetric_difference_update([(add_monomials(a, x), add_monomials(b, y))])
            terms = values
    return terms - {(zero, m), (m, zero)}


def cobar(degree):
    index = (degree + 1).bit_length() - 1
    basis = [monomials(k, index) for k in range(degree + 1)]
    pairs = {pair: i for i, pair in enumerate(
        pair for k in range(1, degree) for pair in product(basis[k], basis[degree-k]))}
    triples = {}
    def image(pair):
        x, y = pair
        terms = [(a, b, y) for a, b in reduced_delta(x)]
        terms.extend((x, a, b) for a, b in reduced_delta(y))
        vector = 0
        for term in terms:
            vector ^= 1 << triples.setdefault(term, len(triples))
        return vector
    d1 = [sum(1 << pairs[p] for p in reduced_delta(m)) for m in basis[degree]]
    d2 = [image(pair) for pair in pairs]
    for m in basis[degree]:
        d_squared = 0
        for p in reduced_delta(m):
            d_squared ^= d2[pairs[p]]
        assert d_squared == 0
    rank1 = len(row_reduce(d1))
    boundaries = row_reduce(d2)
    return (len(d1)-rank1, len(pairs)-rank1-len(boundaries)), triples, boundaries


def audit():
    for degree in range(1, 21):
        (one, two), _, _ = cobar(degree)
        pows = [1 << i for i in range(degree.bit_length())]
        expected_two = sum(x+y == degree for x in pows for y in pows if x <= y and y != 2*x)
        assert (one, two) == (int(degree in pows), expected_two)
    _, triples, boundaries = cobar(17)
    # [xi_1 | xi_1^8 | xi_1^8] represents h_0 h_3^2. Its three
    # entries are primitive, so it is enough to test modulo d(Cobar^2).
    def power(n):
        return (n,) + (0,) * ((17+1).bit_length()-2)
    target = (power(1), power(8), power(8))
    assert all(not reduced_delta(x) for x in target)
    vector = 1 << triples.get(target, len(triples))
    assert len(row_reduce([*boundaries.values(), vector])) == len(boundaries)+1
    print('Cobar ranks agree in filtrations 1 and 2 through internal degree 20; '
          'the cycle h_0 h_3^2 survives modulo all cobar boundaries.')
    for length in range(6, 258, 2):
        if length == 8:
            continue
        bound, modulus = width_bound(length)
        powers = [1 << i for i in range(length.bit_length())]
        if modulus == 2:
            assert all(length-r not in powers for r in range(bound+1))
            assert length-bound-1 in powers
        else:
            two_degrees = {x+y for x in powers for y in powers if x <= y and y != 2*x}
            assert all(length-r not in powers for r in range(1, bound+1))
            assert all(length+1-r not in two_degrees for r in range(2, bound+1))
            assert length-bound in two_degrees
    print('First possible additional source or target relation checked through L=256.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--bottom', type=int)
    parser.add_argument('--rank', type=int)
    args = parser.parse_args()
    if args.bottom is None and args.rank is None:
        audit()
    elif args.rank is None or args.bottom is None or not 2 <= args.rank < args.bottom:
        parser.error('supply 2 <= rank < bottom')
    elif args.bottom in (3, 7):
        print('All bottom squares vanish.')
    else:
        width, q = width_bound(args.bottom + 1)
        d = args.bottom - args.rank
        print(f'Local bottom degree {d}, local CW dimension at most {d+width}, '
              f'character modulus {q}, old filler degree {args.rank+2*args.bottom-1}.')
