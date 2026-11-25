"""Find degree-six tests for fixed finite third homotopy, and transport pair comparisons.

--bottom accepts finite cyclic orders in any cyclic decomposition. JSON with
source, target, coefficient tests maps between two pairs of axes. An axis is
[bottom_order, eta_height], with 0 for a free bottom or for a zero eta action.
JSON with bottom, middle, eta instead computes the paired axes in a primary
decomposition and their bracket coordinates in the input generator basis.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, combinations_with_replacement, product
from math import gcd, lcm
from pathlib import Path
import json


@cache
def factors(n):
    if type(n) is not int or n < 2:
        raise ValueError('finite orders must be integers at least two')
    parts = []
    p = 2
    while p*p <= n:
        e = 0
        while n%p == 0:
            n //= p
            e += 1
        if e:
            parts.append((p,e))
        p = 3 if p == 2 else p+2
    if n>1:
        parts.append((n,1))
    return tuple(parts)


def fixed_bottom(bottom):
    primary = defaultdict(Counter)
    for n in bottom:
        for p,e in factors(n):
            primary[p][e] += 1
    tests = []
    for p,counts in sorted(primary.items()):
        levels = sorted(counts)
        if p == 2:
            tests.append(dict(tester='double_hopf',moore_order=p**levels[0]))
        intervals = [(i,i) for i in levels if counts[i]>=2]
        intervals.extend((i,j) for i,j in zip(levels,levels[1:]) if counts[i]==counts[j]==1)
        for i,j in sorted(intervals):
            tests.append(dict(tester='bracket',bottom=[p**i,p**j],coefficient=p**(i-1)))
    return tests


def entry(source, target):
    a,s = source
    b,t = target
    for n,height in (source,target):
        if type(n) is not int or n<0 or n==1 or type(height) is not int or height<0 or n%2 and height:
            raise ValueError('invalid cyclic order or eta height')
    step = b//gcd(a,b) if b else int(a==0)
    if t and (not s or s>t):
        step = lcm(step,2)
    return step


def transport(source, target, coefficient):
    if len(source)!=2 or len(target)!=2 or type(coefficient) is not int:
        raise ValueError('supply two source and target axes and an integral coefficient')
    a,b = source
    c,d = target
    products = [entry(a,c)*entry(b,d),entry(a,d)*entry(b,c)]
    n = gcd(c[0],d[0])
    period = gcd(n,*(coefficient*m for m in products))
    return dict(matching_degrees=products, target_order=n, generated_period=period,
                image_order=(n//period if n else int(not period)))


def paired_axes(bottom, middle, eta):
    for n in [*bottom,*middle]:
        if type(n) is not int or n!=0 and len(factors(n))!=1:
            raise ValueError('use a primary cyclic decomposition (0 for a free factor)')
    if len(eta)!=len(bottom) or any(len(row)!=len(middle) for row in eta):
        raise ValueError('supply a middle vector per bottom generator')
    for n,row in zip(bottom,eta):
        if any(type(x) is not int or (gcd(2,n)*x%m if m else gcd(2,n)*x)
               for x,m in zip(row,middle)):
            raise ValueError('eta violates the order-two or bottom-order relation')
    columns = sorted((j for j,n in enumerate(bottom) if n%2==0),key=lambda j:(not bottom[j],bottom[j]))
    rows = sorted((i for i,n in enumerate(middle) if n and n%2==0),key=middle.__getitem__)
    matrix = [[bool(eta[j][i]%middle[i]) for j in columns] for i in rows]
    basis = [[int(i==j) for i in range(len(bottom))] for j in range(len(bottom))]
    heights = [0]*len(bottom)
    for c,j in enumerate(columns):
        pivot = next((i for i,row in enumerate(matrix) if row[c]),None)
        if pivot is None:
            continue
        heights[j] = middle[rows[pivot]].bit_length()-1
        for i in range(pivot+1,len(rows)):
            if matrix[i][c]:
                matrix[i] = [x^y for x,y in zip(matrix[i],matrix[pivot])]
        for d,k in enumerate(columns[c+1:],c+1):
            if matrix[pivot][d]:
                matrix[pivot][d] = False
                basis[k] = [x+y for x,y in zip(basis[k],basis[j])]
    pairs = list(combinations(range(len(bottom)),2))
    brackets = [[basis[i][k]*basis[j][l]-basis[i][l]*basis[j][k] for k,l in pairs]
                for i,j in pairs]
    return dict(axes=list(zip(bottom,heights)),bottom_basis=basis,bracket_basis=brackets)


def audit():
    # Enumerate actual allowed bottom coefficients using all compatible middle
    # homomorphisms. Then enumerate every two-by-two matrix on the small axes.
    axes = list(product((2,4),(0,1,2)))
    def maps(a,c):
        n,s = a
        m,t = c
        return [f for f in range(m) if n*f%m==0 and any(
            (2**s*g)%(2**t)==0 and
            ((2**(s-1) if s else 0)*g-(2**(t-1) if t else 0)*f)%(2**t)==0
            for g in range(2**t))]
    allowed = {(a,c):maps(a,c) for a,c in product(axes,repeat=2)}
    pairs = list(combinations_with_replacement(axes,2))
    tested = 0
    for (a,b),(c,d) in product(pairs,repeat=2):
        n = gcd(c[0],d[0])
        dets = {(u*z-v*w)%n for u,v,w,z in product(allowed[a,c],allowed[a,d],allowed[b,c],allowed[b,d])}
        assert gcd(n,*dets)==transport((a,b),(c,d),1)['generated_period']
        tested += 1
    for p in (2,3,5):
        for i,j in combinations_with_replacement(range(1,6),2):
            for u,v in combinations_with_replacement(range(1,6),2):
                f = transport([(p**i,0),(p**j,0)],[(p**u,0),(p**v,0)],p**(i-1))
                assert (f['image_order']>1) == (i<=u<=v<=j)
    for counts in product(range(3),repeat=5):
        levels = [i for i,c in enumerate(counts,1) for _ in range(c)]
        intervals = set(combinations(levels,2))
        minimal = {(i,j) for i,j in intervals if not any((u,v)!=(i,j) and i<=u<=v<=j for u,v in intervals)}
        actual = fixed_bottom([3**i for i in levels])
        assert {(d['bottom'][0],d['bottom'][1]) for d in actual} == {(3**i,3**j) for i,j in minimal}
    # Independent check of the actual basis choices, including shears of
    # generators of unequal orders and the induced change on brackets.
    bottom,middle = [2,4,0],[2,4]
    original_pairs = list(combinations(range(3),2))
    for eta in product(product((0,1),(0,2)),repeat=3):
        data = paired_axes(bottom,middle,eta)
        vectors = data['bottom_basis']
        transformed = [tuple(sum(c*row[j] for c,row in zip(v,eta))%m for j,m in enumerate(middle))
                       for v in vectors]
        # Diagonalized eta with the computed pivot heights must be isomorphic
        # via an actual middle automorphism, tested without row reduction.
        def matches(f,g):
            for value,(_,s) in zip(transformed,data['axes']):
                if tuple((value[0]*x+value[1]*y)%m for x,y,m in zip(f,g,middle)) != (
                        int(s==1),2*int(s==2)):
                    return False
            return True
        assert any(matches((1,k),(l,r)) for k,l,r in product((0,2),(0,1),(1,3)))
        for (i,j),coeffs in zip(original_pairs,data['bracket_basis']):
            for a,b in product(range(2),repeat=2):
                f,g = (a,1,2),(1,b,-1)
                def ev(v,w):
                    return sum(c*y for c,y in zip(v,f))*sum(c*y for c,y in zip(w,g))
                new = ev(vectors[i],vectors[j])-ev(vectors[j],vectors[i])
                assert new==sum(z*(f[k]*g[l]-f[l]*g[k]) for z,(k,l) in zip(coeffs,original_pairs))
    return tested


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--bottom',type=int,nargs='*')
    mode.add_argument('input',type=Path,nargs='?')
    args = parser.parse_args()
    try:
        if args.bottom is not None:
            print(json.dumps(fixed_bottom(args.bottom)))
        elif args.input:
            data = json.loads(args.input.read_text())
            print(json.dumps(transport(**data) if 'source' in data else paired_axes(**data)))
        else:
            print(f'{audit()} decorated pair comparisons checked by all matrices, '
                  '675 prime-power interval tests, 243 fixed-group lists, and 64 paired bases checked.')
    except (TypeError,ValueError) as error:
        parser.error(str(error))
