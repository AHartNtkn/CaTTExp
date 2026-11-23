"""Construct a rational directed-chain model of the full binary Gray surface.

Arguments such as IPI or 1,4,1 give the local globe dimensions in spatial order.
Checks whether this model obstructs the reverse at the characteristic top.
Requires islpy for exact positive-cycle saturation.
"""

from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction
from functools import cache
from itertools import product
from math import lcm

import islpy as isl



def add(vector, key, coefficient):
    n = vector.get(key,0) + coefficient
    if n:
        vector[key] = n
    else:
        vector.pop(key,None)


def differential(word):
    sign = 1
    out = {}
    for i,x in enumerate(word):
        degree = x // 2
        if not degree:
            continue
        for y,c in ((2*degree-1,1),(2*degree-2,-1)):
            add(out, word[:i]+(y,)+word[i+1:],sign*c)
        sign *= (-1)**degree
    return out


class Space:
    def __init__(self):
        self.rows = {}

    def reduce(self, v):
        v = dict(v)
        for p in sorted(self.rows):
            c = v.get(p,0)
            if c:
                for j, val in self.rows[p].items():
                    add(v,j,-c*val)
        return v

    def insert(self, v):
        red = self.reduce(v)
        if red:
            p = min(red)
            self.rows[p] = {i: Fraction(c,red[p]) for i,c in red.items()}

    def kernel(self, n):
        for f in range(n):
            if f not in self.rows:
                v = {f:1}
                for p in sorted(self.rows,reverse=True):
                    c = -sum(a*v.get(j,0) for j,a in self.rows[p].items() if p != j)
                    if c:
                        v[p] = c
                yield v


def positive_cycles(columns):
    """A basis for the span of the nonnegative kernel of a rational matrix."""
    n = len(columns)
    if not n:
        return
    equations = defaultdict(dict)
    for i,v in enumerate(columns):
        for j,a in v.items():
            equations[j][i] = a
    # Coordinates of independent columns with a private row vanish in the cone.
    # ISL also propagates their signs in mixed equations before taking the hull.
    dim = isl.dim_type.set
    base = isl.BasicSet.universe(isl.Space.set_alloc(isl.DEFAULT_CONTEXT,0,n))
    local = isl.LocalSpace.from_space(base.get_space())
    for i in range(n):
        ec = isl.Constraint.inequality_alloc(local).set_coefficient_val(dim,i,1)
        base = base.add_constraint(ec)
    for v in equations.values():
        denominator = lcm(*(Fraction(c).denominator for c in v.values()))
        ec = isl.Constraint.equality_alloc(local)
        for i,c in v.items():
            ec = ec.set_coefficient_val(dim,i,int(denominator*c))
        base = base.add_constraint(ec)
    hull = Space()
    for ec in base.affine_hull().get_constraints():
        assert ec.is_equality() and ec.get_constant_val().is_zero()
        v = {i:ec.get_coefficient_val(dim,i).to_python() for i in range(n)}
        hull.insert({i:c for i,c in v.items() if c})
    yield from hull.kernel(n)


@cache
def quotient(shape):
    by_degree = defaultdict(list)
    for w in product(*(range(2*a+1) for a in shape)):
        by_degree[sum(x//2 for x in w)].append(w)
    rel = {d:Space() for d in by_degree}
    def impose(v):
        if v:
            word = next(iter(v))
            rel[sum(x//2 for x in word)].insert(v)

    for cut in range(1,len(shape)):
        for first in (True,False):
            left, right = shape[:cut], shape[cut:]
            sub, other = (left,right) if first else (right,left)
            subrel,_ = quotient(sub)
            for k in subrel.values():
                for row in k.rows.values():
                    for w in product(*(range(2*a+1) for a in other)):
                        impose({(v+w if first else w+v):c for v,c in row.items()})
    for w in by_degree.get(2,[]):
        if sum(i//2==1 for i in w) == 2:
            impose({w:1})
            impose(differential(w))
    for d,words in sorted(by_degree.items()):
        if d >= 3:
            cols = [rel[d-1].reduce(differential(w)) for w in words]
            for v in positive_cycles(cols):
                # A nontrivial residual positive cycle would invalidate the
                # directed model's identity-endomorphism property in this rank.
                assert not rel[d].reduce({words[i]:c for i,c in v.items()})
    return rel,by_degree


def test(shape):
    if not shape or min(shape) < 1:
        raise ValueError('choose a nonempty list of positive globe dimensions')
    rel,degrees = quotient(shape)
    d = max(degrees)
    w, = degrees[d]
    survives = bool(rel[d].reduce({w:1}))
    boundary = bool(rel[d-1].reduce(differential(w)))
    if d >= 3:
        assert survives == boundary
    for k,sub in rel.items():
        for row in sub.rows.values():
            if not k:
                continue
            image = {}
            for word,c in row.items():
                for a,h in differential(word).items():
                    add(image,a,c*h)
            assert not rel[k-1].reduce(image)
    return survives


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('shapes',nargs='*',default=[''.join(w) for n in range(2,5) for w in product('IP', repeat=n)])
    for shape in parser.parse_args().shapes:
        dims = tuple(1 if a=='I' else 2 for a in shape) if set(shape)<=set('IP') else tuple(map(int,shape.split(',')))
        survives = test(dims)
        assert survives == (not any(a == b == 1 for a,b in zip(dims,dims[1:])))
        print(shape, 'surface reverse excluded' if survives else 'top vanishes in the model', flush=True)
