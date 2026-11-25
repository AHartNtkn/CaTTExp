"""Test whether a two-dimensional pencil of quadratic forms allows the odd Moore probe.

--order uses the displayed optimal detector at a supplied odd prime power.
With no option enumerate all residue-field pencils at orders 3, 5 and 7.
"""
from argparse import ArgumentParser
from itertools import combinations, product
import json

from semistrict_surface_bottom_four import tensor_bracket
from semistrict_surface_quadratic_image import coords, reduction


def echelon(rows, p):
    rows = [list(row) for row in rows]
    pivot = 0
    for col in range(len(rows[0])):
        i = next((i for i in range(pivot,len(rows)) if rows[i][col] % p), None)
        if i is None:
            continue
        rows[pivot], rows[i] = rows[i], rows[pivot]
        v = pow(rows[pivot][col], -1, p)
        base = [v*c % p for c in rows[pivot]]
        rows[pivot] = base
        for j,row in enumerate(rows):
            if j != pivot:
                rows[j] = [(c-row[col]*b) % p for c,b in zip(row,base,strict=True)]
        pivot += 1
    return tuple(tuple(row) for row in rows[:pivot])


def planes(size, p, dimension=2):
    for pivots in combinations(range(size), dimension):
        free = [(i,j) for i,k in enumerate(pivots) for j in range(k+1,size) if j not in pivots]
        for values in product(range(p), repeat=len(free)):
            rows = [[int(j == k) for j in range(size)] for k in pivots]
            for (i,j),c in zip(free,values,strict=True):
                rows[i][j] = c
            yield tuple(tuple(row) for row in rows)


def linear_product(a,b,p):
    return tuple((a[i]*b[j] + (a[j]*b[i] if i != j else 0)) % p for i,j in coords(len(a),2))


def relations_and_probe(forms, r):
    pairs = coords(r,2)
    rows = []
    for letters in coords(r,3):
        row = [0]*(2*r)
        for k in set(letters):
            pair = list(letters)
            pair.remove(k)
            pos = pairs.index(tuple(pair))
            for j,form in enumerate(forms):
                row[2*k+j] = form[pos]
        rows.append(row)
    probe = [0]*(2*r)
    for outer,inner,sign in ([(0,(0,1),1)] if r == 2 else [(2,(0,1),1),(0,(1,2),-1)]):
        for j,form in enumerate(forms):
            probe[2*outer+j] += sign*form[pairs.index(inner)]
    return rows, probe


def field_audit(p):
    r = 3 if p == 3 else 2
    factors = {}
    for ell, in planes(r,p,1):
        for h in planes(r,p):
            forms = echelon([linear_product(ell,v,p) for v in h],p)
            factors[forms] = bool(ell[0]) if r == 2 else len(echelon([ell,*h],p)) == 3
    total = visible = 0
    for forms in planes(len(coords(r,2)),p):
        rows, probe = relations_and_probe(forms,r)
        base = echelon(rows,p)
        assert (len(base) < 2*r) == (forms in factors)
        survives = len(echelon([*base,probe],p)) > len(base)
        assert survives == factors.get(forms,False)
        total += 1
        visible += survives
    return dict(prime=p, pencils=total, with_linear_relation=len(factors), fixed_probe_visible=visible)


def prime_base(n):
    if n < 3 or n % 2 == 0:
        raise ValueError('use an odd prime power')
    p = 3
    while p*p <= n and n % p:
        p += 2
    if p*p > n:
        return n
    while n % p == 0:
        n //= p
    if n != 1:
        raise ValueError('use a single prime power')
    return p


def detector(n):
    p = prime_base(n)
    r = 3 if p == 3 else 2
    keep = [(0,1),(1,2)] if r == 3 else [(0,0),(0,1)]
    pairs = coords(r,2)
    forms = [[int(pair == kept) for pair in pairs] for kept in keep]
    rows, probe = relations_and_probe(forms,r)
    rows += [[n*int(i == j) for i in range(2*r)] for j in range(2*r)]
    _, order = reduction(rows,2*r)
    scaled_order = order([v*(n//p) for v in probe])
    # Read a single degree-three word in the mod-n loop chain algebra.
    # Every quadratic attaching word is killed on its left and right multiples.
    word = (0,1,2) if r == 3 else (1,0,0)
    for i,j in set(pairs)-set(keep):
        for k in range(r):
            for a,b in {(i,j),(j,i)}:
                assert (a,b,k) != word and (k,a,b) != word
    coeff = (tensor_bracket(0,1,2)[word] - tensor_bracket(1,2,0)[word] if r == 3
             else tensor_bracket(0,1,0)[word])
    value = (n//p)*coeff % n
    assert (p*value) % n == 0 and value and scaled_order == p
    return dict(order=n, bottom_rank=r, minimum_group_sizes=[n**r,n*n,n],
                first_hopf_forms=forms, word=[k+1 for k in word],
                top_reading=value, probe_order=scaled_order)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--order',type=int)
    args = parser.parse_args()
    if args.order is not None:
        try:
            print(json.dumps(detector(args.order)))
        except ValueError as error:
            parser.error(str(error))
    else:
        for p in (3,5,7):
            print(json.dumps(field_audit(p)))
            for a in range(1,5):
                detector(p**a)
