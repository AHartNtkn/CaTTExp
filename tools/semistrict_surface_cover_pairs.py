"""Degree-six brackets with independently translated inputs.

--orbit N LEFT RIGHT reads the cyclic shift on N binary coordinates. LEFT and
RIGHT are bit masks giving one module generator for each permitted input.
--telescope D PERIOD ATTACH NUMERATOR reads a bracket on the localized
two-sphere-wedge telescope. The coefficient is NUMERATOR/d^j for any j >= 0,
and ATTACH is the top relation (0 for no relation). PERIOD is surface data.
"""
from argparse import ArgumentParser
from itertools import combinations, product
from math import comb, gcd, isqrt
from pathlib import Path
import json

from semistrict_surface_lens_squares import row_reduce


def permute(mask, positions):
    return sum(1 << target for i, target in enumerate(positions) if mask & (1 << i))


def tensor(n, left, right):
    return sum(right << (i*n) for i in range(n) if left & (1 << i))


def exterior(n, mask):
    return sum((((mask >> (i*n+j)) ^ (mask >> (j*n+i))) & 1) << k
               for k, (i, j) in enumerate(combinations(range(n), 2)))


def orbit(n, left, right):
    if n < 1 or not (0 <= left < 2**n and 0 <= right < 2**n):
        raise ValueError('supply a positive sheet count and bit masks fitting the sheets')
    diagonal = [((i+1) % n)*n + (j+1) % n for i, j in product(range(n), repeat=2)]
    residual = [((i+1) % n)*n + j for i, j in product(range(n), repeat=2)]
    rows = {tensor(n, left, right)}
    while True:
        basis = list(row_reduce(rows).values())
        rows = basis + [permute(v, shift) for v in basis for shift in (diagonal, residual)]
        if len(row_reduce(rows)) == len(basis):
            break
    return list(row_reduce(exterior(n, v) for v in basis).values())


def telescope(d, period, attach, numerator):
    if d < 2 or d % 2 or min(period, attach) < 0:
        raise ValueError('use even d >= 2 and nonnegative periods')
    def localized(k):
        while k and gcd(k, d) > 1:
            k //= gcd(k, d)
        return k
    def belongs(k):
        return numerator % k == 0 if k else numerator == 0
    raw = localized(attach)
    surface = localized(gcd(period, attach))
    return dict(raw_period=raw, surface_period=surface,
                raw_fills=belongs(raw), surface_fills=belongs(surface))


def principal(prime, relation, face):
    """Divide two Laurent polynomials supplied as [t-power,u-power,coefficient] terms."""
    if prime < 3 or any(prime % i == 0 for i in range(2, isqrt(prime)+1)):
        raise ValueError('the bottom exponent must be an odd prime')
    def primitive(terms):
        values = {}
        for i, j, c in terms:
            values[i, j] = (values.get((i, j), 0)+c) % prime
        values = {ij: c for ij, c in values.items() if c}
        if not values:
            return {}
        lo = [min(e[k] for e in values) for k in (0, 1)]
        return {(i-lo[0], j-lo[1]): c for (i, j), c in values.items()}
    divisor, rem = primitive(relation), primitive(face)
    if not divisor:
        return not rem
    a, b = max(divisor)
    inv = pow(divisor[a, b], -1, prime)
    while rem:
        i, j = max(rem)
        if i < a or j < b:
            return False
        scale = inv * rem[i, j]
        for (u, v), c in divisor.items():
            pos = (u+i-a, v+j-b)
            rem[pos] = (rem.get(pos, 0)-scale*c) % prime
            if not rem[pos]:
                del rem[pos]
    return True


def audit():
    checked = 0
    for n in range(1, 5):
        rotation = [(i+1) % n for i in range(n)]
        def powers(v):
            values = []
            for _ in range(n):
                values.append(v)
                v = permute(v, rotation)
            return values
        for left, right in product(range(2**n), repeat=2):
            actual = orbit(n, left, right)
            expected = [exterior(n, tensor(n, x, y)) for x, y in product(powers(left), powers(right))]
            assert len(row_reduce(actual)) == len(row_reduce(expected)) == len(row_reduce(actual+expected))
            checked += 1
    # Compare finite-stage divisibility in successive images of the wedge.
    # A multiple of d kills the d-primary part of any of these periods in <=4 steps.
    cases = 0
    for d, period, attach, numerator in product((2, 6, 10, 12), range(13), range(13), range(-8, 9)):
        result = telescope(d, period, attach, numerator)
        for k, field in ((attach, 'raw_fills'), (gcd(attach, period), 'surface_fills')):
            possible = any((numerator*(-d)**j) % k == 0 for j in range(5)) if k else numerator == 0
            assert result[field] == possible
        cases += 1
    # A separate quotient substitutes u=1+t, where Laurent denominators
    # are units. Clear the common monomial before evaluating coefficients.
    relation = [(0, 1, 1), (0, 0, -1), (1, 0, -1)]
    comparisons = 0
    for coeffs in product(range(3), repeat=6):
        positions = [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (0, 2)]
        face = [(i-2, j-1, c) for (i, j), c in zip(positions, coeffs)]
        subst = [0]*3
        for (i, j), c in zip(positions, coeffs):
            for k in range(j+1):
                subst[i+k] += comb(j, k)*c
        assert principal(3, relation, face) == all(x % 3 == 0 for x in subst)
        comparisons += 1
    return checked, cases, comparisons


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--orbit', type=int, nargs=3, metavar=('N', 'LEFT', 'RIGHT'))
    mode.add_argument('--telescope', type=int, nargs=4, metavar=('D', 'PERIOD', 'ATTACH', 'NUMERATOR'))
    mode.add_argument('--ideal', type=Path, help='JSON with prime, relation and face')
    args = parser.parse_args()
    try:
        if args.ideal:
            raw = principal(**json.loads(args.ideal.read_text()))
            print(json.dumps(dict(raw_fills=raw, surface='fills' if raw else 'fills iff its prime bracket test fills')))
        elif args.orbit:
            basis = orbit(*args.orbit)
            print(json.dumps(dict(bracket_basis=basis, dimension=len(basis))))
        elif args.telescope:
            print(json.dumps(telescope(*args.telescope)))
        else:
            orbits, queries, ideals = audit()
            print(f'{orbits} independent-translate spans and {queries} localized comparisons and {ideals} Laurent ideal tests checked.')
    except ValueError as error:
        parser.error(str(error))
