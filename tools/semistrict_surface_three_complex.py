"""Extract a necessary smaller binary filling from a bottom class on a 3-complex.

orders lists Moore orders, with zero denoting a two-sphere. brackets uses
[i,j,k,c] for c[[i,j],k]. hopf uses [i,j,c] for the pair Hopf if i < j,
or the double Hopf if i == j. Indices start at one.
"""

import json
from argparse import ArgumentParser
from collections import Counter
from itertools import product
from math import gcd
from pathlib import Path

from semistrict_surface_bottom_four import tensor_bracket
from semistrict_surface_moore_triples import upper_pair


def primary_parts(n):
    p = 2
    while p * p <= n:
        q = 1
        while n % p == 0:
            n //= p
            q *= p
        if q > 1:
            yield p, q
        p += 1 if p == 2 else 2
    if n > 1:
        yield n, n


def separating_order(g, s, t):
    if g:
        return next(((p, q) for p, q in primary_parts(g) if s % q or t % q), None)
    if s or t:
        q = 2
        while s % q == t % q == 0:
            q *= 2
        return 2, q
    return None


def read(data):
    orders = data['orders']
    if any(type(n) is not int or n < 0 or n == 1 for n in orders):
        raise ValueError('use zero for a sphere or an integer Moore order at least two')

    def valid(indices, c):
        if type(c) is not int or any(type(i) is not int or not 1 <= i <= len(orders) for i in indices):
            raise ValueError('cells require in-range indices and integral multiplicities')

    hopf = Counter()
    for i, j, c in data.get('hopf', []):
        valid([i, j], c)
        if i > j:
            raise ValueError('put Hopf indices in increasing order')
        hopf[i,j] += c

    words = Counter()
    for i, j, k, c in data.get('brackets', []):
        valid([i, j, k], c)
        for w, value in tensor_bracket(i, j, k).items():
            words[w] += c * value
    for support in sorted({tuple(sorted(set(w))) for w in words if words[w]}):
        x, y, *other = support
        if other:
            z, = other
            s, t = words[y, x, z], words[y, z, x]
        else:
            s, t = words[y, x, x], words[x, y, y]
        g = gcd(*(orders[i-1] for i in support))
        residue = separating_order(g, s, t)
        if residue:
            p, q = residue
            folds = [s+t, t-2*s, s-2*t] if other else [s,t]
            c = next((value for value in folds if value % q), None)
            # A nonzero folded coordinate generates an ideal containing q/p.
            # In the common fold kernel s generates that same socle at three.
            coefficient = s if c is None else c
            h = gcd(coefficient, q)
            multiplier = ((q//p)//h * pow(coefficient//h, -1, q//h)) % (q//h)
            assert multiplier * coefficient % q == q//p
            return dict(raw=False, implies_filling=dict(
                probe='alternating' if p == 3 else 'repeated', order=q, support=support,
                coordinates=[s % q, t % q], route='common fold kernel' if c is None else 'pair coordinate',
                coefficient=coefficient % q, multiplier=multiplier))

    for (i,j), c in sorted(hopf.items()):
        if c % 2 and gcd(orders[i-1], orders[j-1]) % 2 == 0:
            return dict(raw=False, implies_filling=dict(
                probe='pair Hopf', order=2, support=sorted({i,j}),
                route='diagonal and exact pair projection' if i == j else 'reduce both letters'))
    return dict(raw=True, implies_filling=None)


def audit():
    # Compare the support order with the integral bottom-cell tensor
    # presentation, including the infinite-order and relatively prime cases.
    from semistrict_surface_reversible_five import quotient
    probes = Counter()
    checked = 0
    for orders in product((0,2,3,4,6,9), repeat=3):
        rel = [[n,0] for n in orders if n] + [[0,n] for n in orders if n]
        for s,t in product((-9,-4,-1,0,2,3,6), repeat=2):
            result = read(dict(orders=orders, brackets=[[1,2,3,s],[2,3,1,t]]))
            assert result['raw'] == (not any(quotient(rel,[s,t])))
            if not result['raw']:
                info = result['implies_filling']
                q = info['order']
                assert all(n % q == 0 for n in orders)
                probes[info['probe']] += 1
            checked += 1
    # On a homogeneous even wedge, directly expand U,V under every map
    # to two letters and test the joint kernel over the actual ring.
    matrices = 0
    for q in (2,4,8):
        cuts = set()
        for a,b,c in product(product(range(q),repeat=2), repeat=3):
            cuts.update((i % q,j % q) for i,j in zip(upper_pair(a,b,c), upper_pair(b,c,a), strict=True))
            matrices += 1
        assert all(any((s*i+t*j) % q for i,j in cuts)
                   for s,t in product(range(q), repeat=2) if s or t)
    # Compute the tensor-cell boundaries before reducing coefficients. The
    # first stable Hopf survives when H3 / 2 is nonzero and integral H5 is zero.
    for m,n in product((0,2,3,4,6,9), repeat=2):
        d4 = [value for value in (m, -n) if value]
        d5 = [n, m] if m and n else []
        assert not d5 or (any(d5) and sum(a*b for a,b in zip(d4,d5,strict=True)) == 0)
        assert bool(any(quotient([[v] for v in [2,*d4]], [1]))) == (gcd(m,n) % 2 == 0)
        for i,j in ((1,1),(1,2),(2,2)):
            for c in (-2,-1,0,1,2):
                h = gcd((m,n)[i-1], (m,n)[j-1], 2)
                assert read(dict(orders=[m,n],hopf=[[i,j,c]]))['raw'] == (not any(quotient([[h]],[c])))
    assert probes.keys() == {'repeated','alternating'}
    return checked, matrices


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path)
    args = parser.parse_args()
    if args.input:
        try:
            print(json.dumps(read(json.loads(args.input.read_text()))))
        except (ValueError, KeyError) as error:
            parser.error(str(error))
    else:
        checked, matrices = audit()
        print(f'{checked} mixed cubic classes, {matrices} even-order substitutions and 540 Hopf coordinates checked.')
