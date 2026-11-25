"""Degree-five bottom image modulo second Hopfs, from first Hopf relations.

rank counts chosen bottom generators. relations give rows in lexicographic
(i,j), i <= j: the diagonal is a Hopf value and an off-diagonal is a bracket.
An optional face lists [outer letter, i, j, coefficient] with 1-based indices,
for the bracket of the quadratic (i,j) with that outer letter.
"""
import json
from argparse import ArgumentParser
from itertools import combinations_with_replacement, product
from math import gcd, lcm
from pathlib import Path

from semistrict_surface_divisible_squares import diagonalize


def coords(rank, weight):
    return list(combinations_with_replacement(range(rank), weight))


def unit(size, index):
    return [int(i == index) for i in range(size)]


def reduction(rows, width):
    matrix, columns, used = diagonalize(rows, 0, width)
    orders = [abs(matrix[i][i]) if i < used else 0 for i in range(width)]

    def order(vector):
        value = 1
        for j, n in enumerate(orders):
            c = sum(x * columns[i][j] for i, x in enumerate(vector))
            if c and not n:
                return 0
            if n:
                value = lcm(value, n // gcd(c, n))
        return value
    return [n for n in orders if n != 1], order


def presentation(rank, relations):
    pairs = coords(rank, 2)
    width = len(pairs)
    rows = []
    for k in range(rank):
        for r in relations:
            rows.append([0]*(k*width) + list(r) + [0]*((rank-k-1)*width))
    for letters in coords(rank, 3):
        row = [0]*(rank*width)
        for outer in set(letters):
            rest = list(letters)
            rest.remove(outer)
            row[outer*width + pairs.index(tuple(rest))] = 1
        rows.append(row)
    return rows


def read(data):
    rank, relations = data['rank'], data['relations']
    if type(rank) is not int or rank < 0:
        raise ValueError('rank must be nonnegative')
    pairs = coords(rank, 2)
    if any(len(row) != len(pairs) or any(type(c) is not int for c in row) for row in relations):
        raise ValueError('invalid quadratic relation row')
    orders, order = reduction(presentation(rank, relations), rank*len(pairs))
    result = {'cyclic_orders': orders, 'bottom_generated_by_second_hopfs': not orders}
    if 'face' in data:
        vector = [0]*(rank*len(pairs))
        for k,i,j,c in data['face']:
            if any(type(a) is not int for a in (k,i,j,c)) or not (1 <= k <= rank and 1 <= i <= j <= rank):
                raise ValueError('face rows need an outer letter, ordered inner pair, and integer coefficient')
            vector[(k-1)*len(pairs) + pairs.index((i-1,j-1))] += c
        result['face_order_mod_hopfs_in_canonical_complex'] = order(vector)
    return result


def word_check(rank, relations, vectors):
    # In degree three the loop model imposes both left and right products
    # with each attaching word. Compare orders of actual commutators.
    pairs = coords(rank, 2)
    words = list(product(range(rank), repeat=3))
    left, right = [], []
    for k in range(rank):
        for i,j in pairs:
            inner = {(i,j),(j,i)}
            left.append([int(w[0] == k and w[1:] in inner) for w in words])
            right.append([int(w[-1] == k and w[:2] in inner) for w in words])
    boundaries = []
    for block in (left, right):
        for k in range(rank):
            for row in relations:
                boundaries.append([sum(c*block[k*len(pairs)+t][j] for t,c in enumerate(row))
                                   for j in range(len(words))])
    _, word_order = reduction(boundaries,len(words))
    _, source_order = reduction(presentation(rank, relations),rank*len(pairs))
    for v in vectors:
        tensor = [sum(c*(r[j]-l[j]) for c,r,l in zip(v,right,left,strict=True)) for j in range(len(words))]
        assert word_order(tensor) == source_order(v)


def audit():
    checked = 0
    vectors = list(product((-1,0,1), repeat=6))
    for row in product((-1,0,1),repeat=3):
        for relations in ([row], [row, (2,0,0)], [row,(2,0,0),(0,0,3)]):
            word_check(2, relations, vectors)
            checked += len(vectors)
    pairs = coords(3,2)
    width = 3*len(pairs)
    vectors3 = [unit(width,i) for i in range(width)]
    vectors3 += [[(j*(i+1)+j*j) % 5 - 2 for j in range(width)] for i in range(5)]
    for keep in combinations_with_replacement(range(len(pairs)),2):
        rows = [unit(len(pairs), i) for i in range(len(pairs)) if i not in keep]
        word_check(3,rows,vectors3)
        checked += len(vectors3)
    return checked


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
        print(f'{audit()} commutator orders checked against loop word boundaries.')
