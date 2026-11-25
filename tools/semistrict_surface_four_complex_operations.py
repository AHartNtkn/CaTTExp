"""Compute degree-five Whitehead and Hopf subgroups from bottom and middle groups.

JSON keys: bottom, middle (cyclic orders, 0 for Z), quadratic (one vector in
middle coordinates per lexicographic unordered bottom pair, including diagonals).
Optional face: one vector in middle coordinates per operation, in the order
eta, bracket with first bottom letter, bracket with second bottom letter, ...
"""
import json
from argparse import ArgumentParser
from itertools import combinations_with_replacement, product
from math import gcd, prod
from pathlib import Path

from semistrict_surface_divisible_squares import diagonalize
from semistrict_surface_quadratic_image import reduction


def subgroup(rows, width, generators):
    """Relations among the named elements, by eliminating the ambient columns."""
    generators = list(dict.fromkeys(tuple(v) for v in generators if any(v)))
    size = len(generators)
    if not size:
        return []
    lifted = [[0]*size + list(row) for row in rows]
    for i, vector in enumerate(generators):
        lifted.append([int(i == j) for j in range(size)] + list(vector))
    matrix, _, used = diagonalize(lifted, size, width)
    return reduction([row[:size] for row in matrix[used:]], size)[0]


def operation_presentation(bottom, middle, quadratic):
    if any(type(n) is not int or n < 0 or n == 1 for n in [*bottom, *middle]):
        raise ValueError('cyclic orders must be zero or at least two')
    rank, size = len(bottom), len(middle)
    pairs = list(combinations_with_replacement(range(rank), 2))
    def validate(v):
        if len(v) != size or any(type(x) is not int for x in v):
            raise ValueError('expected one integral coordinate per middle generator')
    values = dict(zip(pairs, quadratic, strict=True))
    for (i, j), v in values.items():
        validate(v)
        n = bottom[i]
        order = n * (2 if n % 2 == 0 else 1) if i == j else gcd(n, bottom[j])
        for c, m in zip(v, middle, strict=True):
            if (order*c % m if m else order*c):
                raise ValueError('quadratic value violates its bottom order')

    width = (rank+1)*size
    units = [[int(i == j) for j in range(size)] for i in range(size)]
    def block(k, v):
        return [0]*(k*size) + list(v) + [0]*((rank-k)*size)
    rows = []
    for k, n in enumerate([2, *bottom]):
        for j, m in enumerate(middle):
            d = gcd(n, m)
            if d:
                rows.append(block(k, [d*c for c in units[j]]))
    for letters in combinations_with_replacement(range(rank), 3):
        row = [0]*width
        for k in set(letters):
            inner = list(letters)
            inner.remove(k)
            for j, v in enumerate(values[tuple(inner)]):
                row[(k+1)*size+j] += v
        support = sorted(set(letters))
        if len(support) == 2:
            for j, v in enumerate(values[tuple(support)]):
                row[j] -= v
        rows.append(row)
    bottom_gens = [block(k,v) for v in quadratic for k in range(rank+1)]
    eta_gens = [block(0,v) for v in units]
    return rows,bottom_gens,eta_gens


def solve(bottom, middle, quadratic, face=None):
    rows,bottom_gens,eta_gens = operation_presentation(bottom,middle,quadratic)
    rank,size = len(bottom),len(middle)
    width = (rank+1)*size
    ambient, order = reduction(rows, width)
    bottom_group = subgroup(rows, width, bottom_gens)
    joined_group = subgroup(rows, width, bottom_gens + eta_gens)
    result = dict(operation_group=ambient, bottom_image=bottom_group,
                  joined_kernel=joined_group, forces_binary_reflection=not bottom_group)
    if face is not None:
        if len(face) != rank+1:
            raise ValueError('face needs eta and one bracket row per bottom letter')
        if any(len(v) != size or any(type(x) is not int for x in v) for v in face):
            raise ValueError('expected one integral coordinate per middle generator')
        flat = [c for v in face for c in v]
        result['raw_order'] = order(flat)
        for label, generators in [('bottom',bottom_gens), ('joined', bottom_gens + eta_gens)]:
            result['in_'+label] = reduction(rows + generators, width)[1](flat) == 1
    return result


def check():
    # Independent character enumeration. Impose the composition identities on
    # all actual elements of C2^2 and C2^2, then count restrictions to images.
    vectors = list(product(range(2),repeat=2))
    forms = list(product(vectors, repeat=3))
    for coeffs in forms:
        def linear(c,v):
            return sum(x*y for x,y in zip(c,v)) % 2
        def q(x):
            return tuple((x[0]*a+x[0]*x[1]*b+x[1]*c) % 2
                         for a,b,c in zip(*coeffs))
        def polar(x,y):
            return tuple(a^b^c for a,b,c in zip(q(x),q(y),q(tuple(i^j for i,j in zip(x,y)))))
        readings, bottom_readings, joined_readings = set(), set(), set()
        for h,t,u in product(vectors, repeat=3):
            def bracket(b,x):
                return (linear(t,b)*x[0]+linear(u,b)*x[1]) % 2
            if any(bracket(q(x),x) or
                   bracket(q(x),y)^bracket(polar(x,y),x)^linear(h,polar(x,y))
                   for x,y in product(vectors, repeat=2)):
                continue
            readings.add((h,t,u))
            restricted = tuple(linear(l,v) for l in (h,t,u) for v in coeffs)
            bottom_readings.add(restricted)
            joined_readings.add((restricted,h))
        result = solve([2,2],[2,2],coeffs)
        for key, chars in [('operation_group',readings), ('bottom_image',bottom_readings),
                           ('joined_kernel',joined_readings)]:
            assert prod(result[key]) == len(chars)
    # A Moore wedge with mixed orders plus a retracted third sphere.
    bottom = [4,6]
    middle = [8,2,12,0]
    q = [[1,0,0,0],[0,1,0,0],[0,0,1,0]]
    result = solve(bottom,middle,q)
    assert prod(result['bottom_image']) == 2**5
    assert prod(result['joined_kernel']) == 2**6
    assert prod(result['operation_group']) == 2**6*4*6
    # Nonprimitive quadratic image in a free generator. The mixed relation
    # makes its bracket have finite order; distinguish membership from order.
    for n in range(1,13):
        result = solve([0],[0],[[n]],[[0],[1]])
        assert result['raw_order'] == n and result['in_joined'] == (n == 1)
        assert prod(result['bottom_image']) == (2 if n % 2 else 1)
        assert prod(result['joined_kernel']) == 2
    assert solve([0],[0],[[0]],[[0],[1]])['raw_order'] == 0
    for pairs in range(1,5):
        letters = range(2*pairs)
        q = [[int(i//2 == j//2 == k) for k in range(pairs)]
             for i,j in combinations_with_replacement(letters,2)]
        assert not solve([2]*len(letters),[2]*pairs,q)['bottom_image']
    return len(forms)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path)
    args = parser.parse_args()
    if args.input:
        try:
            print(json.dumps(solve(**json.loads(args.input.read_text()))))
        except (KeyError, TypeError, ValueError) as error:
            parser.error(str(error))
    else:
        print(f'{check()} quadratic maps checked by exhaustive character readings; '
              'mixed orders, nonprimitive images and disjoint nonsplit blocks checked.')
