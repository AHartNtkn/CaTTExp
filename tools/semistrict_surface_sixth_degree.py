"""Compute and detect bottom differences on 2-connected reversible five-complexes.

JSON input has bottom and middle cyclic orders (0 means infinite), eta rows
giving the middle value on each bottom generator, and hopfs and brackets giving
a signed operation difference. Brackets are in lexicographic pair order.
Optional dimension m>=3 changes the bottom degree. Brackets occur only at m=3.
"""
from argparse import ArgumentParser
from itertools import combinations, product
from math import gcd, isqrt, lcm
from pathlib import Path
import json

from semistrict_surface_quadratic_image import reduction


def coordinates(bottom, middle, eta, hopfs, brackets, dimension=3):
    if type(dimension) is not int or dimension < 3:
        raise ValueError('bottom degree must be at least three')
    if any(type(n) is not int or n < 0 or n == 1 for n in [*bottom,*middle]):
        raise ValueError('cyclic orders must be zero or at least two')
    if len(eta) != len(bottom) or len(hopfs) != len(bottom):
        raise ValueError('each bottom generator needs an eta image and Hopf coefficient')
    for n,row in zip(bottom,eta):
        if len(row) != len(middle):
            raise ValueError('each eta row needs one entry per middle generator')
        for x,b in zip(row,middle):
            if type(x) is not int or (2*x%b if b else 2*x) or (n*x%b if b else n*x):
                raise ValueError('eta images must be two-torsion and respect bottom orders')
    pairs = list(combinations(range(len(bottom)),2)) if dimension == 3 else []
    if len(brackets) != len(pairs) or any(type(c) is not int for c in [*hopfs,*brackets]):
        raise ValueError('supply integral coefficients in the prescribed operation basis')
    bits = [sum(c*row[j] for c,row in zip(hopfs,eta))%gcd(2,b) for j,b in enumerate(middle)]
    orders = [gcd(bottom[i],bottom[j]) for i,j in pairs]
    values = [c%n if n else c for c,n in zip(brackets,orders)]
    order = 2 if any(bits) else 1
    for c,n in zip(values,orders):
        if c:
            order = lcm(order,n//gcd(n,c) if n else 0)
    if any(bits):
        j = bits.index(1)
        return dict(order=order,hopf_bits=bits,bracket_values=values,
                    tester='Moore',bottom_map=[row[j]%2 for row in eta],middle_coordinate=j)
    for (i,j),n,c in zip(pairs,orders,values):
        if not c:
            continue
        if not n:
            # Any level at which the free coefficient survives will do.
            q = 2
            while c%q == 0:
                q *= 2
            p = 2
        else:
            # A prime of the additive order is exactly a primary component
            # where the full coefficient survives.
            order_here = n//gcd(c,n)
            p = next((d for d in range(2,isqrt(order_here)+1) if order_here%d == 0),order_here)
            q = p
            while n%(q*p) == 0:
                q *= p
        return dict(order=order,hopf_bits=bits,bracket_values=values,tester='pair',
                    bottom_coordinates=[i,j],level=q,reading=c%q,
                    socle=q//p)
    return dict(order=order,hopf_bits=bits,bracket_values=values,tester=None)


def homogeneous(order, rank, top_orders, bracket_images, face, period):
    """Test a top difference at zero first eta, given the measured pair period."""
    pairs = rank*(rank-1)//2
    if type(order) is not int or order < 2 or type(rank) is not int or rank < 0:
        raise ValueError('a finite homogeneous bottom group is required')
    if type(period) is not int or period <= 0 or order%period:
        raise ValueError('period must divide the bottom order')
    if any(type(t) is not int or t < 0 or t == 1 for t in top_orders):
        raise ValueError('top orders must be zero or at least two')
    if len(bracket_images) != pairs:
        raise ValueError('supply every pair bracket in lexicographic order')
    width = len(top_orders)
    for v in [face,*bracket_images]:
        if len(v) != width or any(type(c) is not int for c in v):
            raise ValueError('expect integral vectors with one entry per top summand')
    if any((order*c%t if t else order*c) for v in bracket_images for c,t in zip(v,top_orders)):
        raise ValueError('bracket image violates its bottom order')
    rows = [[t*int(i == j) for j in range(width)] for i,t in enumerate(top_orders) if t]
    kernel = [[period*c for c in v] for v in bracket_images]
    return dict(raw_fills=reduction(rows,width)[1](face)==1,
                binary_fills=reduction(rows+kernel,width)[1](face)==1)


def stable(bottom, top_orders, double_hopfs, face, threshold):
    """Conditional exact kernel for m>=4; finite means every finite Moore level."""
    if not (type(threshold) is int and threshold >= 0 or threshold in ('finite','all')):
        raise ValueError("threshold must be nonnegative, 'finite', or 'all'")
    if any(type(n) is not int or n < 0 or n == 1 for n in [*bottom,*top_orders]):
        raise ValueError('cyclic orders must be zero or at least two')
    if len(bottom) != len(double_hopfs):
        raise ValueError('supply one double Hopf image per bottom generator')
    width = len(top_orders)
    if any(len(v) != width or any(type(c) is not int for c in v) for v in [face,*double_hopfs]):
        raise ValueError('expect integral vectors with one entry per top summand')
    rows = [[t*int(i == j) for j in range(width)] for i,t in enumerate(top_orders) if t]
    kernel = []
    for n,v in zip(bottom,double_hopfs):
        if any((gcd(2,n)*c%t if t else gcd(2,n)*c) for c,t in zip(v,top_orders)):
            raise ValueError('double Hopf violates its order')
        if threshold == 'all' or n and (threshold == 'finite' or (n & -n).bit_length()-1 <= threshold):
            kernel.append(v)
    return dict(raw_fills=reduction(rows,width)[1](face)==1,
                binary_fills=reduction(rows+kernel,width)[1](face)==1)


def audit():
    checked = 0
    # Start in the full operation subgroup of the four-skeleton, with the
    # independent fourth spheres and each Moore eta. Quotient by eta of the
    # actual five-disk boundaries; all pair components start independently.
    for bottom in ([2,4],[3,9],[0,6],[0,0],[4,2,3]):
        middle = [2,4]
        pairs = list(combinations(range(len(bottom)),2))
        active = [i for i,n in enumerate(bottom) if n%2 == 0]
        width = len(active)+2+len(pairs)
        def unit(i):
            return [int(i==j) for j in range(width)]
        horders = [2]*(len(active)+2) + [gcd(bottom[i],bottom[j]) for i,j in pairs]
        base = [[c*n for c in unit(i)] for i,n in enumerate(horders) if n]
        for choices in product(((0,0),(1,0),(0,2),(1,2)),repeat=len(active)):
            eta = [[0,0] for _ in bottom]
            rows = base.copy()
            for k,(i,row) in enumerate(zip(active,choices)):
                eta[i] = row
                v = unit(k)
                for j,t in enumerate(row):
                    v[len(active)+j] -= t
                rows.append(v)
            _,raw_order = reduction(rows,width)
            for h in product(range(2),repeat=len(bottom)):
                for b in product((-2,0,1),repeat=len(pairs)):
                    face = [h[i] for i in active]+[0,0]+list(b)
                    ans = coordinates(bottom,middle,eta,h,b)
                    assert ans['order'] == raw_order(face)
                    if ans['tester'] == 'Moore':
                        f = ans['bottom_map']
                        assert sum(x*y for x,y in zip(f,h))%2 == 1
                        assert all(n*x%2 == 0 for n,x in zip(bottom,f))
                    elif ans['tester'] == 'pair':
                        pair = tuple(ans['bottom_coordinates'])
                        q = ans['level']
                        assert all(bottom[i]%q == 0 for i in pair)
                        assert b[pairs.index(pair)]%q == ans['reading'] != 0
                        assert any(k*ans['reading']%q == ans['socle'] for k in range(q))
                    else:
                        assert ans['order'] == 1
                    checked += 1
    for m in range(4,15):
        assert coordinates([4],[4],[[2]],[1],[],m)['order'] == 1
        assert coordinates([4],[2],[[1]],[1],[],m)['tester'] == 'Moore'
    # Check pushforwards against actual subgroup generation with mixed torsion.
    images = [[2,1],[0,1],[4,0]]
    for period in (1,2,4):
        subgroup = {(0,0)}
        for v in images:
            subgroup = {((x+period*k*v[0])%8,(y+period*k*v[1])%2)
                        for x,y in subgroup for k in range(4)}
        for f in product(range(8),range(2)):
            ans = homogeneous(4,3,[8,2],images,f,period)
            assert ans['binary_fills'] == (f in subgroup) and ans['raw_fills'] == (f==(0,0))
    bottom,top,images = [4,6,8],[4,2],[[2,0],[0,1],[2,1]]
    for t in (0,1,2,3,'finite','all'):
        expected = set()
        for xs in product(*(range(n) for n in bottom)):
            if type(t) is int and any(2**t*x%n for x,n in zip(xs,bottom)):
                continue
            expected.add(tuple(sum(c*y for c,y in zip(xs,col))%n for col,n in zip(zip(*images),top)))
        for f in product(*(range(n) for n in top)):
            assert stable(bottom,top,images,f,t)['binary_fills'] == (f in expected)
    assert not stable([0],[4],[[2]],[2],'finite')['binary_fills']
    assert stable([0],[4],[[2]],[2],'all')['binary_fills']
    return checked


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        try:
            if 'period' in data:
                answer = homogeneous(**data)
            elif 'threshold' in data:
                answer = stable(**data)
            else:
                answer = coordinates(**data)
        except (TypeError,ValueError) as error:
            parser.error(str(error))
        print(json.dumps(answer))
    else:
        print(f'{audit()} signed five-complex faces checked against attaching rows; '
              'stable double Hopfs and cyclic pair-kernel pushforwards checked.')
