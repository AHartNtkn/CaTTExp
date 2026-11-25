"""Compute the degree-five operation pairing for the first Hopf map x -> x^(p+1).

--prime p --modulus c0,c1,...,1 specifies a monic irreducible polynomial,
low coefficients first. Elements are encoded by the base-p digits of their
polynomial coefficients. Default checks several fields against cubic relations.
"""
import json
from argparse import ArgumentParser
from functools import cache
from math import gcd, isqrt

from semistrict_surface_hopf_pencils import character_equations
from semistrict_surface_lens_squares import row_reduce
from semistrict_surface_moore_detectors import echelon
from semistrict_surface_quadratic_image import coords


class Field:
    def __init__(self, p, modulus):
        if p < 2 or any(p % d == 0 for d in range(2,isqrt(p)+1)):
            raise ValueError('the characteristic must be prime')
        if len(modulus) < 4 or modulus[-1] != 1 or any(not 0 <= c < p for c in modulus):
            raise ValueError('use a monic polynomial of degree at least three over the field')
        self.p, self.m, self.modulus = p,len(modulus)-1,modulus
        self.size = p**self.m
        # Rabin test, using Euclidean gcd in F_p[T].
        def poly_gcd(a,b):
            while b:
                while a and len(a) >= len(b):
                    c = a[-1]*pow(b[-1],-1,p) % p
                    shift = len(a)-len(b)
                    for i,t in enumerate(b):
                        a[i+shift] = (a[i+shift]-c*t) % p
                    while a and not a[-1]:
                        a.pop()
                a,b = b,a
            return len(a)-1
        power = p
        for i in range(1,self.m+1):
            power = self.exp(power,p)
            if i <= self.m//2:
                residue = list(self.digits(self.add(power,p,-1)))
                while residue and not residue[-1]:
                    residue.pop()
                if poly_gcd(list(modulus),residue) != 0:
                    raise ValueError('the modulus is reducible')
        if power != p:
            raise ValueError('the modulus is reducible')

    @cache
    def digits(self, x):
        return tuple(x//self.p**i % self.p for i in range(self.m))

    def pack(self, digits):
        return sum((x % self.p)*self.p**i for i,x in enumerate(digits))

    def add(self, x,y,sign=1):
        return self.pack(a+sign*b for a,b in zip(self.digits(x),self.digits(y)))

    @cache
    def mul(self, x,y):
        v = [0]*(2*self.m-1)
        for i,a in enumerate(self.digits(x)):
            for j,b in enumerate(self.digits(y)):
                v[i+j] += a*b
        for i in range(len(v)-1,self.m-1,-1):
            for j,c in enumerate(self.modulus[:-1]):
                v[i-self.m+j] -= v[i]*c
        return self.pack(v[:self.m])

    def exp(self, x,n):
        y = 1
        while n:
            if n & 1:
                y = self.mul(y,x)
            x = self.mul(x,x)
            n //= 2
        return y

    @cache
    def trace(self,x):
        value = 0
        for _ in range(self.m):
            value = self.add(value,x)
            x = self.exp(x,self.p)
        assert value < self.p
        return value


def calculate(p,modulus):
    field = Field(p,tuple(modulus))
    m = field.m
    units = [p**i for i in range(m)]
    q = lambda x:field.exp(x,p+1)
    def theta(b,x):
        return field.add(field.mul(b,field.exp(x,p*p)),field.mul(field.exp(b,p),x),-1)
    pairs = coords(m,2)
    forms = list(zip(*(field.digits(q(units[i]) if i == j else
                        field.add(field.add(q(field.add(units[i],units[j])),q(units[i]),-1),q(units[j]),-1))
                      for i,j in pairs)))
    tables = [[theta(b,x) for x in units] for b in units]
    tr_forms = [[field.trace(field.mul(a,v)) for row in tables for v in row] for a in units]
    realized = len(echelon(tr_forms,p))
    if p == 2:
        masks = [sum(c << j for j,c in enumerate(f)) for f in forms]
        rels = row_reduce(character_equations(m,masks))
        for values in tr_forms:
            char = sum(values[i*m+j] << ((j+1)*m+i) for i in range(m) for j in range(m))
            assert all(not ((row & char).bit_count() % 2) for row in rels.values())
        dim = m*(m+1)-len(rels)
        # A reading of a middle Hopf survives iff its vector extends the row space.
        assert all(len(row_reduce([*rels.values(),1 << i])) == len(rels) for i in range(m))
    else:
        cubics = coords(m,3)
        index = {t:j for j,t in enumerate(cubics)}
        rows = [[0]*(m*m) for _ in cubics]
        for i,f in enumerate(forms):
            for pair,c in zip(pairs,f):
                for j in range(m):
                    rows[index[tuple(sorted((*pair,j)))]][i*m+j] += c
        assert all(sum(v*t for v,t in zip(row,char)) % p == 0 for row in rows for char in tr_forms)
        dim = m*m-len(echelon(rows,p))
    assert dim == realized == (2 if m == 3 else m)
    ranks = {}
    for a in range(1,field.size):
        mat = [[field.trace(field.mul(a,v)) for v in row] for row in tables]
        rk = len(echelon(mat,p))
        ranks[rk] = ranks.get(rk,0)+1
    # The old face [[1,T],1].
    b = field.add(field.exp(p,p),p)
    repeat = theta(b,1)
    assert repeat == field.add(p,field.exp(p,p*p),-1) and repeat
    if m == 3:
        assert set(ranks) == {0,3}
    elif gcd(3,m) == 1:
        assert set(ranks) == {m-1}
    return dict(prime=p,degree=m,bottom_dimension=dim,trace_pairing_ranks=ranks,
                repeated_value=repeat)


def audit():
    cases = [(2,[1,1,0,1]),(2,[1,1,0,0,1]),(2,[1,0,1,0,0,1]),
             (2,[1,1,0,0,0,0,1]),(2,[1,1,0,0,0,0,0,1]),
             (3,[1,2,0,1]),(3,[2,1,0,0,1]),(5,[1,1,0,1])]
    readings = 0
    for p,poly in cases:
        readings += sum(calculate(p,poly)['trace_pairing_ranks'].values())
    from semistrict_surface_hopf_pencils import analyze
    # The effective middle image of two elementary bottom generators has
    # at most three coordinates. Enumerate every possible subspace.
    from semistrict_surface_moore_detectors import planes
    spaces = 0
    for s in range(4):
        for basis in planes(3,2,s):
            masks = [sum(c << j for j,c in enumerate(f)) for f in basis]
            assert analyze(2,masks)['undetected_dimension'] == 0
            spaces += 1
    return readings,spaces


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--prime',type=int)
    parser.add_argument('--modulus')
    args = parser.parse_args()
    try:
        if args.prime is None and args.modulus is None:
            print('%d trace pairing ranks and all %d two-variable subspaces checked.' % audit())
        elif args.prime is not None and args.modulus is not None:
            print(json.dumps(calculate(args.prime,list(map(int,args.modulus.split(','))))))
        else:
            parser.error('supply both the prime and modulus')
    except ValueError as error:
        parser.error(str(error))
