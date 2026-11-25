"""Test the cyclic first Hopf polynomial for a possible degree-five binary failure.

JSON input: rank, order (zero for an infinite cyclic image), coefficients
in lexicographic unordered-pair order of the first Hopf polynomial.
"""
import json
from argparse import ArgumentParser
from itertools import combinations_with_replacement
from math import gcd
from pathlib import Path


def parity(n):
    return n.bit_count() % 2


def factor(rank, coefficients):
    """Find two homogeneous linear factors over F2, by linear substitution.

    A linear factor vanishes on its kernel. A quadratic vanishing there is
    formally divisible by it, since homogeneous quadratics are determined
    by their values on binary vectors.
    """
    pairs = list(combinations_with_replacement(range(rank), 2))
    def value(x):
        return sum(c for (i,j), c in zip(pairs, coefficients, strict=True) if x >> i & x >> j & 1) % 2
    polar = [0]*rank
    diagonal = 0
    for (i,j),c in zip(pairs,coefficients,strict=True):
        if c % 2:
            if i == j:
                diagonal |= 1 << i
            else:
                polar[i] |= 1 << j
                polar[j] |= 1 << i
    span = {0}
    for row in polar:
        if row not in span:
            if len(span) == 4:
                return None
            span.update(value ^ row for value in tuple(span))
    if len(span) == 1:
        return diagonal, diagonal
    # The polar form of a product of two independent linear factors has
    # their span as its row space. This leaves only three possible factors.
    for a in sorted(span - {0}):
        e = a & -a
        b = 0
        for i in range(rank):
            v = 1 << i
            coefficient = value(v) if a & v else value(e ^ v) ^ value(e)
            b |= coefficient << i
        actual = [(((a >> i) & (b >> j)) ^ ((a >> j) & (b >> i) if i != j else 0)) & 1
                  for i,j in pairs]
        if actual == [c % 2 for c in coefficients]:
            return a,b
    return None


def read(data):
    rank, order, coeffs = data['rank'], data['order'], data['coefficients']
    if type(rank) is not int or rank < 0 or type(order) is not int or order < 0:
        raise ValueError('supply a nonnegative rank and cyclic order')
    if len(coeffs) != rank*(rank+1)//2 or any(type(c) is not int for c in coeffs):
        raise ValueError('supply one integral coefficient per unordered pair, including diagonals')
    if gcd(order,*coeffs) != 1:
        raise ValueError('the listed first Hopf values must generate the stated cyclic group')
    factors = None if order % 2 else factor(rank, coeffs)
    return dict(canonical_bottom_order=2 if factors else 1,
                factors=None if factors is None else [[i+1 for i in range(rank) if v >> i & 1] for v in factors],
                forced_binary_reflection=factors is None)


def relation_test(rank, masks):
    """Solve directly for lambda from the one- and two-input Whitehead identities."""
    size = 1 << rank
    f = [parity(sum(1 << j for j,m in enumerate(masks) if x & m == m)) for x in range(size)]
    basis = {}
    def impose(bits, target):
        while bits:
            k = bits.bit_length()-1
            if k not in basis:
                basis[k] = bits,target
                return True
            old, val = basis[k]
            bits ^= old
            target ^= val
        return not target
    for x in range(size):
        if f[x] and not impose(x,0):
            return False
        for y in range(size):
            b = f[x ^ y] ^ f[x] ^ f[y]
            if not impose((y if f[x] else 0) ^ (x if b else 0), b):
                return False
    return True


def repeated_check(n):
    # Keep x^2 and xy+yx in the middle group of the two-Moore tester.
    # The 4-disk rows are y^2 and n*x^2. Read the word yxx over Z/n.
    from semistrict_surface_bottom_four import tensor_bracket
    word = (1,0,0)
    for inner,c in [((1,1),1), ((0,0),n)]:
        for k in range(2):
            assert not any(w == word and c % n for w in ((k,*inner),(*inner,k)))
    return (n//2)*tensor_bracket(0,1,0)[word] % n


def smash_checks(top):
    # Tensor cell (i,j) of positive-dimensional projective cells, before suspension.
    def boundary(i,j):
        terms = {}
        if i % 2 == 0:
            terms[i-1,j] = 2
        if j % 2 == 0:
            terms[i,j-1] = 2*(-1)**i
        return terms
    cells = [(i,j) for i in range(1,top+1) for j in range(1,top+1)]
    # Sq^2(xy) = x^2 y^2. An integral cycle in degree four must have
    # zero (2,2) coefficient. Exercise the boundary, including orientations.
    from itertools import product
    cells4 = [c for c in cells if sum(c) == 4]
    checks = 0
    for coefficients in product(range(-3,4),repeat=len(cells4)):
        chain = dict(zip(cells4,coefficients,strict=True))
        image = {d: sum(c*boundary(*s).get(d,0) for s,c in chain.items()) for d in cells if sum(d)==3}
        assert (not any(image.values())) == (chain.get((2,2),0) == 0)
        checks += 1
    assert boundary(2,1) == {(1,1):2} and boundary(1,2) == {(1,1):-2}
    assert boundary(2,2) == {(1,2):2,(2,1):2}
    return checks


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    args = parser.parse_args()
    if args.input:
        try:
            print(json.dumps(read(json.loads(args.input.read_text()))))
        except (KeyError, ValueError) as error:
            parser.error(str(error))
    else:
        checked = split = 0
        for rank in range(1,5):
            pairs = list(combinations_with_replacement(range(rank),2))
            for form in range(1,1 << len(pairs)):
                coeffs = [form >> k & 1 for k in range(len(pairs))]
                masks = [(1 << i) | (1 << j) for (i,j),c in zip(pairs,coeffs,strict=True) if c]
                answer = read(dict(rank=rank,order=2,coefficients=coeffs))
                assert (answer['canonical_bottom_order'] == 2) == relation_test(rank,masks)
                split += answer['canonical_bottom_order'] == 2
                checked += 1
        for a in range(1,13):
            assert repeated_check(2**a) == 2**(a-1)
        cycles = smash_checks(2) + smash_checks(4)
        print(f'{checked} binary quadratic forms checked, {split} factorizable; {cycles} integral smash chains checked.')
