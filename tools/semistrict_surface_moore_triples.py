"""Read the binary degree-five kernel on equal odd-order Moore wedges from its two parameters."""

from argparse import ArgumentParser
from collections import defaultdict
from itertools import permutations, product
from pathlib import Path
import json

from semistrict_surface_bottom_four import tensor_bracket
from semistrict_surface_reversible_five import quotient


def upper_pair(a, b, c):
    """Coefficients of yxx and xyy in the adjoint Hurewicz tensor [[a,b],c]."""
    def coefficient(i, j, k):
        return ((a[i]*b[j] + b[i]*a[j])*c[k]
                - c[i]*(a[j]*b[k] + b[j]*a[k]))
    return coefficient(1, 0, 0), coefficient(0, 1, 1)


def three_block(p, q, period, extra):
    if p % period == q % period == 0:
        return True
    return extra and (p+q) % period == 0 and (3*p) % period == 0


def read(data):
    n, d = data['order'], data.get('pair_period')
    extra = data.get('extra_three')
    if type(n) is not int or n < 3 or n % 2 == 0:
        raise ValueError('the Moore order must be odd and at least three')
    if (d is not None and (type(d) is not int or d < 1 or n % d)
            or extra is not None and type(extra) is not bool or extra and (d is None or d % 3)):
        raise ValueError('the period must divide the order; an extra three-letter relation needs 3 | period')
    tor = defaultdict(int)
    for i,j,c in data.get('tor', []):
        if not all(type(x) is int for x in (i,j,c)) or not 1 <= i < j:
            raise ValueError('Tor entries are [smaller letter, larger letter, signed coefficient]')
        tor[i,j] += c
    blocks = defaultdict(lambda: [0, 0])
    for i, j, k, weight in data.get('brackets', []):
        if not all(type(x) is int for x in (i, j, k, weight)) or min(i,j,k) < 1:
            raise ValueError('use positive integer letter indices and integer coefficients')
        letters = tuple(sorted({i,j,k}))
        if len(letters) == 1:
            continue
        x, y, *rest = letters
        values = tensor_bracket(i, j, k)
        if not rest:
            coords = values[y,x,x], values[x,y,y]
        else:
            # U=[[x,y],z] and V=[[y,z],x].  Coefficients at yxz and yzx are +1,0 and 0,+1.
            z, = rest
            coords = values[y,x,z], values[y,z,x]
        for a, c in enumerate(coords):
            blocks[letters][a] += c*weight
    joined = all(c % n == 0 for c in tor.values())
    raw = joined and all(all(c % n == 0 for c in row) for row in blocks.values())
    if d is None:
        binary = raw if raw or not joined else None
    else:
        def fits(include_extra):
            return joined and all(three_block(*row, d, include_extra and len(key) == 3)
                                  for key, row in blocks.items())
        binary = fits(bool(extra))
        if extra is None and d % 3 == 0 and not binary and fits(True):
            binary = None
    return dict(raw=raw, binary=binary, joined=joined)


def prime_probes(n):
    remaining = n
    primes = []
    p = 3
    while p*p <= remaining:
        if remaining % p == 0:
            primes.append(p)
            while remaining % p == 0:
                remaining //= p
        p += 2
    if remaining > 1:
        primes.append(remaining)
    return {p: ([[1, 2, 3, n//p], [2, 3, 1, -(n//p)]] if p == 3 else [[2, 1, 1, n//p]])
            for p in primes}


def audit():
    pair_x, pair_y = (1,0), (0,1)
    assert upper_pair(pair_x, pair_y, pair_x) == (1,0)
    assert upper_pair(pair_x, pair_y, pair_y) == (0,1)
    assert upper_pair(pair_x, pair_x, pair_y) == (-2,0)
    matrices = 0
    for n in (3, 5, 9):
        cuts = set()
        for col in product(product(range(n), repeat=2), repeat=3):
            a,b,c = col
            u = upper_pair(a,b,c)
            v = upper_pair(b,c,a)
            cuts.update((m % n, k % n) for m,k in zip(u,v,strict=True))
            matrices += 1
        kernel = {(p,q) for p,q in product(range(n),repeat=2)
                  if all((p*m+q*k) % n == 0 for m,k in cuts)}
        assert kernel == {(p,q) for p,q in product(range(n),repeat=2)
                          if three_block(p,q,n,n % 3 == 0)}
    # Independently compute the class in the word tensor for signed sums with six orderings.
    word_orders = list(permutations((1,2,3)))
    signs = {w: (-1)**sum(w[i] > w[j] for i in range(3) for j in range(i+1,3))
             for w in word_orders}
    for weights in product(range(-1,2),repeat=6):
        terms = [[*w,c] for w,c in zip(word_orders,weights,strict=True)]
        coeffs = {w: sum(c*tensor_bracket(*word)[w] for word,c in zip(word_orders,weights,strict=True))
                  for w in word_orders}
        result = read(dict(order=9,pair_period=9,extra_three=True,brackets=terms))
        assert result['raw'] == all(c % 9 == 0 for c in coeffs.values())
        alternating = any(all((coeffs[w] - t*signs[w]) % 9 == 0 for w in word_orders)
                          for t in (0,3,6))
        assert result['binary'] == alternating
    # The prime tests jointly characterize zero kernel in each permitted parameter table.
    tables = 0
    for n in range(3,82,2):
        for d in range(1,n+1):
            if n % d:
                continue
            for extra in ([False,True] if d % 3 == 0 else [False]):
                results = [read(dict(order=n,pair_period=d,extra_three=extra,brackets=w))
                           for w in prime_probes(n).values()]
                assert all(not r['raw'] for r in results)
                assert all(not r['binary'] for r in results) == (d == n and not extra)
                tables += 1
    for n in range(3, 36, 2):
        # The Moore smash has d3 = [n,-n] (with chosen cell orientations)
        # and the next boundary is n times the primitive kernel generator.
        for c in range(2*n):
            assert read(dict(order=n, tor=[[1,2,c]]))['joined'] == (not any(quotient([[n,n]], [c,c])))
    return matrices,tables


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path)
    parser.add_argument('--probes', type=int, metavar='ODD_ORDER')
    args = parser.parse_args()
    if args.probes is not None:
        if args.probes < 3 or args.probes % 2 == 0:
            parser.error('supply an odd Moore order at least three')
        print(json.dumps(prime_probes(args.probes)))
    elif args.input:
        try:
            print(json.dumps(read(json.loads(args.input.read_text()))))
        except ValueError as error:
            parser.error(str(error))
    else:
        matrices,tables = audit()
        print(f'{matrices} rank-two substitutions, 729 signed tensor expansions and {tables} kernel tables checked.')
