"""Degree-five testers on k vector letters and binomial(k,2) alternating letters.

--rank k --order n computes the three simultaneous minimum detecting groups.
A JSON input with prime, rank (source bottom dimension), forms (coefficient
rows in lexicographic unordered-pair order) and face (middle-by-bottom bracket
coefficients) constructs a substitution detecting the face at an odd prime.
"""
import json
from argparse import ArgumentParser
from itertools import combinations
from math import comb, isqrt
from pathlib import Path

from semistrict_surface_moore_detectors import echelon, linear_product
from semistrict_surface_quadratic_image import coords


def linear_system(rows, targets, width, p):
    reduced = echelon([list(r)+[v] for r,v in zip(rows,targets,strict=True)],p)
    solution = [0]*width
    for row in reduced:
        pivot = next(i for i,c in enumerate(row) if c)
        if pivot == width:
            return None
        solution[pivot] = row[-1]
    return solution


def substitute(prime, rank, forms, face):
    p = prime
    if type(p) is not int or p < 3 or p % 2 == 0 or any(p % d == 0 for d in range(3,isqrt(p)+1,2)):
        raise ValueError('the substitution requires an odd prime')
    if type(rank) is not int or rank < 1 or not forms:
        raise ValueError('a positive bottom rank and independent middle forms are required')
    pairs = coords(rank,2)
    size = len(forms)
    if any(len(f) != len(pairs) for f in forms) or len(face) != size or any(len(v) != rank for v in face):
        raise ValueError('incompatible quadratic or bracket dimensions')
    if any(type(c) is not int for row in [*forms,*face] for c in row):
        raise ValueError('coefficients must be integers')
    if len(echelon(forms,p)) != size:
        raise ValueError('the middle forms must be independent')
    cubics = coords(rank,3)
    indices = {c:i for i,c in enumerate(cubics)}
    equations = [[0]*(size*rank) for _ in cubics]
    for i, form in enumerate(forms):
        for pair, c in zip(pairs,form,strict=True):
            for j in range(rank):
                equations[indices[tuple(sorted((*pair,j)))]][i*rank+j] += c
    flat = [v for row in face for v in row]
    reading = linear_system([*equations,flat],[0]*len(cubics)+[1],size*rank,p)
    if reading is None:
        return {'raw_nonzero':False}
    reading = [reading[i:i+rank] for i in range(0,len(reading),rank)]
    basis = echelon(reading,p)
    k = len(basis)
    pivots = [next(i for i,c in enumerate(row) if c) for row in basis]
    middle = [[u[i] for i in pivots] for u in reading]
    active = [[sum(row[s]*f[j] for row,f in zip(middle,forms)) % p for j in range(len(pairs))]
              for s in range(k)]
    edges = list(combinations(range(k),2))
    matrix = [[0]*(len(edges)*rank) for _ in range(k*len(pairs))]
    for e,(a,b) in enumerate(edges):
        for j in range(rank):
            unit = [int(i == j) for i in range(rank)]
            for s,t,sign in [(a,b,1),(b,a,-1)]:
                for col,c in enumerate(linear_product(basis[t],unit,p)):
                    matrix[s*len(pairs)+col][e*rank+j] = sign*c
    target = [c for form in active for c in form]
    skew = linear_system(matrix,target,len(edges)*rank,p)
    assert skew is not None
    skew = [skew[i:i+rank] for i in range(0,len(skew),rank)]
    # Check the literal image of every source quadratic against the chosen
    # middle map and evaluate the whole submitted face on the target pairing.
    pulled = [[0]*len(pairs) for _ in range(k)]
    for (a,b),v in zip(edges,skew,strict=True):
        for s,t,sign in [(a,b,1),(b,a,-1)]:
            for j,c in enumerate(linear_product(basis[t],v,p)):
                pulled[s][j] += sign*c
    assert [[c % p for c in f] for f in pulled] == active
    value = sum(face[i][j]*middle[i][s]*basis[s][j]
                for i in range(size) for j in range(rank) for s in range(k)) % p
    assert value == 1
    return dict(raw_nonzero=True, tester_rank=max(4,k), active_axes=basis,
                alternating_axes=skew, middle_map=middle, reading=value)


def word_check(k,n):
    if k < 4 or n < 2:
        raise ValueError('use rank at least four and order at least two')
    edges = list(combinations(range(k),2))
    dim = k+len(edges)
    def weight(i,j,t):
        if i >= k or j >= k or t < k:
            return 0
        a,b = edges[t-k]
        return int((i,j) == (a,b))-int((i,j) == (b,a))
    def quadratic(i,j):
        if i >= k or j < k:
            return None,0
        a,b = edges[j-k]
        if i == b:
            return a,1
        if i == a:
            return b,-1
        return None,0
    checked = 0
    for i,j in coords(dim,2):
        index,sign = quadratic(i,j)
        for t in range(dim):
            left,right = weight(t,i,j),weight(i,j,t)
            if i != j:
                left += weight(t,j,i)
                right += weight(j,i,t)
            assert (left - sign*int(index == t)) % n == 0 and right % n == 0
            checked += 2
    assert weight(0,1,k) == 1
    return dict(rank=k, order=n, cyclic_factor_counts=[dim,k,1],
                signed_words=2*comb(k,2), checked_multiples=checked)


def audit():
    checked = sum(word_check(k,n)['checked_multiples']
                  for k in range(4,8) for n in (2,3,4,5,8,9,25))
    # Independent raw orders from the integral four-complex presentation.
    from semistrict_surface_four_complex_operations import solve
    count = 0
    for p in (3,5,7):
        families = [[[1,0,0],[0,1,0]], [[1,0,0],[0,0,1]],
                    [[1,1,0],[0,1,1]], [[0,1,0],[0,0,1],[1,0,0]]]
        for forms in families:
            q = list(zip(*forms))
            for slot in range(2*len(forms)):
                face = [[int(2*i+j == slot) for j in range(2)] for i in range(len(forms))]
                result = substitute(p,2,forms,face)
                raw = solve([p,p],[p]*len(forms),q,[[0]*len(forms),*zip(*face)])
                assert result['raw_nonzero'] == (raw['raw_order'] == p)
                count += 1
    # Rank-four syzygy, including variable identifications and changed
    # middle basis. Every call verifies the pulled-back attaching rows.
    for p in (3,5):
        k = 4
        pairs = coords(k,2)
        basis = [[int(i == j) for j in range(k)] for i in range(k)]
        forms = [[0]*len(pairs) for _ in range(k)]
        for e,(a,b) in enumerate(combinations(range(k),2)):
            v = [((e+1)**(i+1)+e*i) % p for i in range(k)]
            for s,t,sign in [(a,b,1),(b,a,-1)]:
                for i,c in enumerate(linear_product(basis[t],v,p)):
                    forms[s][i] += sign*c
        forms[0] = [a+b for a,b in zip(forms[0],forms[1])]
        assert substitute(p,k,forms,[[int(i == j == 0) for j in range(k)] for i in range(k)])['raw_nonzero']
    return checked,count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path)
    parser.add_argument('--rank',type=int)
    parser.add_argument('--order',type=int)
    args = parser.parse_args()
    try:
        if args.input:
            print(json.dumps(substitute(**json.loads(args.input.read_text()))))
        elif args.rank is not None and args.order is not None:
            print(json.dumps(word_check(args.rank,args.order)))
        elif args.rank is not None or args.order is not None:
            parser.error('supply both --rank and --order')
        else:
            print('%d signed attaching-word checks and %d integral face comparisons passed.' % audit())
    except (TypeError,ValueError) as error:
        parser.error(str(error))
