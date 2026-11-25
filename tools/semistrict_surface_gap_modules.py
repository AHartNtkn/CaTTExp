"""Degree-six bracket comparisons in a circle wedged with an odd Moore space.

JSON contains prime, relations (a list of boundaries), and face. Each boundary
is a list of [coefficient, first_shift, second_shift] Whitehead products.
Only simultaneous translations of each attached boundary are raw relations.
"""
from argparse import ArgumentParser
from itertools import product
import json
from math import isqrt
from pathlib import Path


def add(left, right, p, factor=1, shift=0):
    out = left.copy()
    for j, a in right.items():
        i = j + shift
        c = (out.get(i, 0) + factor*a) % p
        if c:
            out[i] = c
        else:
            out.pop(i, None)
    return out


def divide(left, right, p):
    # Remove the lowest monomial from each polynomial as a Laurent unit.
    if not left:
        return {}, {}
    low = min(left)
    gap = max(right)-min(right)
    inv = pow(right[max(right)], -1, p)
    rem, quot = left.copy(), {}
    while rem and max(rem)-low >= gap:
        j = max(rem)-max(right)
        c = rem[max(rem)]*inv % p
        quot[j] = c
        rem = add(rem, right, p, -c, j)
    return quot, rem


def subtract_multiple(row, coeffs, pivot, p):
    result = []
    for x, y in zip(row, pivot, strict=True):
        for j, c in coeffs.items():
            x = add(x, y, p, -c, j)
        result.append(x)
    return result


def contains(rows, face, p):
    # Each Euclidean pair operation preserves the Laurent span. The remaining
    # rows generate exactly its submodule with zero pivot coordinate.
    rows = list(rows)
    for j in range(len(face)):
        index = next((i for i, row in enumerate(rows) if row[j]), None)
        if index is None:
            if face[j]:
                return False
            continue
        pivot = rows.pop(index)
        for i, row in enumerate(rows):
            while row[j]:
                coeffs, _ = divide(pivot[j], row[j], p)
                pivot, row = row, subtract_multiple(pivot, coeffs, row, p)
            rows[i] = row
        coeffs, rem = divide(face[j], pivot[j], p)
        if rem:
            return False
        face = subtract_multiple(face, coeffs, pivot, p)
    return True


def coordinates(terms, p):
    result = {}
    for c, i, j in terms:
        if i == j:
            continue
        if i > j:
            i, j, c = j, i, -c
        gap = j-i
        result[gap] = add(result.get(gap, {}), {i: c}, p)
    return {g: poly for g, poly in result.items() if poly}


def compare(prime, relations, face):
    if prime < 3 or any(prime % i == 0 for i in range(2, isqrt(prime)+1)):
        raise ValueError('use an odd prime')
    rows = [coordinates(terms, prime) for terms in [*relations, face]]
    gaps = sorted(set().union(*rows))
    matrix = [[row.get(gap, {}) for gap in gaps] for row in rows]
    raw = contains(matrix[:-1], matrix[-1], prime)
    return dict(distances=gaps, raw_fills=raw,
                surface='fills' if raw else 'fills iff its prime bracket test fills')


def audit():
    # Impose t^3=1 by separate *top disks* on two distances. Enumerate the
    # finite F_3 span of translates of the remaining relation independently.
    p = 3
    orbit = [(1,0,0,2,2,0), (0,1,0,0,2,2), (0,0,1,2,0,2)]
    subgroup = {tuple(sum(c*r[i] for c, r in zip(cs, orbit)) % p for i in range(6))
                for cs in product(range(p), repeat=3)}
    relations = [[(1,-1,-1+g),(-1,2,2+g)] for g in (1,2)]
    relations.append([(1,0,1),(-1,0,2),(1,3,1)])  # c1-(1+t)c2
    count = 0
    for cs in product(range(p), repeat=6):
        face = [(c, i-3, i-3+g) for c, (g, i) in zip(cs, product((1,2), range(3)))]
        assert compare(p, relations, face)['raw_fills'] == (cs in subgroup)
        count += 1
    assert not compare(3, [[(1,0,1)]], [(1,0,2)])['raw_fills']
    assert compare(3, [[(1,0,1)]], [(1,5,4)])['raw_fills']
    return count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, nargs='?')
    args = parser.parse_args()
    if args.input:
        print(json.dumps(compare(**json.loads(args.input.read_text()))))
    else:
        print(f'{audit()} coupled Laurent comparisons checked against explicit finite subgroup generation.')
