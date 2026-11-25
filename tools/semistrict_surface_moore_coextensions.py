"""Compute the joined top subgroup from Moore coextensions and pair periods.

Orders use 0 for infinity. Supply bottom, top, hopfs, first_level (null for no
filled coextension) and coextensions, one top vector per even finite bottom
summand. At bottom degree three also supply brackets and pair_periods in
lexicographic pair order. Optional face tests membership at a written difference.
"""
import json
from argparse import ArgumentParser
from itertools import combinations, product
from math import gcd
from pathlib import Path

from semistrict_surface_four_complex_operations import subgroup
from semistrict_surface_quadratic_image import reduction


def solve(bottom, top, hopfs, coextensions, first_level, dimension=4,
          brackets=(), pair_periods=(), face=None):
    if type(dimension) is not int or dimension < 3:
        raise ValueError('bottom degree must be at least three')
    if first_level is not None and (type(first_level) is not int or first_level < 1):
        raise ValueError('first_level must be a positive integer or null')
    if any(type(n) is not int or n < 0 or n == 1 for n in [*bottom,*top]):
        raise ValueError('orders must be zero or at least two')
    width = len(top)
    rows = [[n*int(i==j) for j in range(width)] for i,n in enumerate(top) if n]
    for v in [*hopfs,*coextensions,*brackets,*([face] if face is not None else [])]:
        if len(v) != width or any(type(c) is not int for c in v):
            raise ValueError('expected an integral vector in top coordinates')
    raw_order = reduction(rows,width)[1]
    if any(raw_order(v) not in (1,2) for v in hopfs):
        raise ValueError('a suspended Hopf has order at most two')
    kernel = list(hopfs)
    modulo_hopfs = reduction(rows+kernel,width)[1]
    even = [n for n in bottom if n and n%2 == 0]
    if len(even) != len(coextensions):
        raise ValueError('supply one coextension per finite even bottom summand')
    for n,v in zip(even,coextensions):
        if modulo_hopfs(v) not in (1,2):
            raise ValueError('the double of a coextension must lie among the suspended Hopfs')
        if n%4 == 0 and raw_order(v) not in (1,2):
            raise ValueError('a coextension at a multiple of four has order at most two')
        if first_level is not None and (n & -n).bit_length()-1 >= first_level:
            kernel.append(v)
    pairs = list(combinations(bottom,2)) if dimension == 3 else []
    if len(brackets) != len(pairs) or len(pair_periods) != len(pairs):
        raise ValueError('supply one bracket and period per unstable pair')
    for (s,t),v,d in zip(pairs,brackets,pair_periods):
        n = gcd(s,t)
        if type(d) is not int or d < 0 or n and (not d or n%d):
            raise ValueError('a pair period must define a subgroup of its cyclic bracket')
        if n and raw_order([n*c for c in v]) != 1:
            raise ValueError('the bracket violates its order')
        kernel.append([d*c for c in v])
    result = dict(kernel_orders=subgroup(rows,width,kernel),
                  coextension_levels=[(n & -n).bit_length()-1 for n in even])
    if face is not None:
        result.update(raw_fills=raw_order(face)==1,joined_fills=reduction(rows+kernel,width)[1](face)==1)
    return result


def audit():
    # A cellular map of Moore spaces has bottom and upper degrees f,g
    # with n*f=m*g. The upper degree reads the secondary class on the pinch.
    maps = 0
    for r,s in product(range(1,7),repeat=2):
        n,m = 2**r,2**s
        images = set()
        for f in range(m):
            g,rem = divmod(n*f,m)
            if rem:
                continue
            images.add(g%2)
            # The same map acting on the source bottom element killed by two.
            assert (n//2*f)%m == (m//2)*(g%2)
            maps += 1
        assert (1 in images) == (r<=s)
    checks = 0
    bottom,top = [2,4,0],[4,4,3]
    hopfs = [[2,0,0]]
    lifts = [[1,0,0],[0,2,0]]
    brackets = [[2,2,0],[0,2,0],[0,1,0]]
    for first,periods in product((1,2,3,None),((2,2,4),(1,2,2),(2,1,1))):
        args = dict(bottom=bottom,top=top,hopfs=hopfs,coextensions=lifts,first_level=first,
                    dimension=3,brackets=brackets,pair_periods=periods)
        expected = set()
        for h,u,v,x,y,z in product(range(2),range(4),range(2),range(2),range(2),range(4)):
            if u and (first is None or first>1) or v and (first is None or first>2):
                continue
            if any(c%d for c,d in zip((x,y,z),periods)):
                continue
            expected.add(((2*h+u+2*x)%4,(2*v+2*x+2*y+z)%4,0))
        for face in product(*(range(n) for n in top)):
            answer = solve(**args,face=face)
            assert answer['joined_fills'] == (face in expected)
            assert answer['raw_fills'] == (face==(0,0,0))
            checks += 1
    # All choices of half and nullhomotopy have the same membership modulo h.
    for first in (1,2,None):
        for face in product(range(4),range(4)):
            opts = dict(bottom=[2,4],top=[4,4],hopfs=[[2,0]],first_level=first,face=face)
            assert solve(**opts,coextensions=[[1,0],[0,2]]) == solve(**opts,coextensions=[[3,0],[2,2]])
    return maps,checks


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    args = parser.parse_args()
    if args.input:
        try:
            print(json.dumps(solve(**json.loads(args.input.read_text()))))
        except (TypeError,ValueError) as error:
            parser.error(str(error))
    else:
        maps,checks = audit()
        print(f'{maps} cellular Moore maps and {checks} mixed top comparisons checked, '
              'including changes of coextension lifts.')
