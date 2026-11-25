"""Normalize a cyclic-top Postnikov invariant over a finite primary lower type.

Use elementary integral chain coordinates. hom_orders and ext_orders are
exponents h,e in cyclic orders p^h in H_{j+1} and p^e in H_j. level is s in
the top coefficient order p^s. hom and ext are the corresponding residues.
"""
from argparse import ArgumentParser
from itertools import product
from math import isqrt
import json
from pathlib import Path


def valuation(x,p):
    if not x:
        raise ValueError('valuation requires a nonzero integer')
    height = 0
    while x % p == 0:
        x //= p
        height += 1
    return height


def check_prime(p):
    if type(p) is not int or p < 2 or any(p % i == 0 for i in range(2,1+isqrt(p))):
        raise ValueError('use a prime')


def normalize(data):
    p,s = data['prime'],data['level']
    check_prime(p)
    if type(s) is not int or s < 1:
        raise ValueError('level must be positive')
    order = p**s
    hom,ext = [],[]
    for key,parts in [('hom',hom),('ext',ext)]:
        for e,c in zip(data[key+'_orders'],data[key],strict=True):
            if type(e) is not int or e < 1 or type(c) is not int:
                raise ValueError('supply positive homology exponents and integral coordinates')
            if key == 'hom' and c*p**e % order:
                raise ValueError('a character coordinate violates the order of its homology generator')
            parts.append(c % (order if key == 'hom' else p**min(e,s)))
    h = max((s-valuation(c,p) for c in hom if c),default=0)
    canonical = [c//(p**(s-h)) for c in hom]
    if h:
        unit = pow(next(c for c in canonical if c % p),-1,p**h)
        canonical = [c*unit % (p**h) for c in canonical]
    delay = max((e-valuation(c,p) for e,c in zip(data['ext_orders'],ext,strict=True) if c),default=0)
    return dict(tower_level=h, character=canonical, delay=delay, agreement_level=s+delay)


def towers(p, orders):
    check_prime(p)
    s = max(orders,default=1)
    chars = set()
    for residues in product(*(range(p**e) for e in orders)):
        hom = [r*(p**(s-e)) for e,r in zip(orders,residues,strict=True)]
        entry = normalize(dict(prime=p,level=s,hom_orders=orders,hom=hom,ext_orders=[],ext=[]))
        if entry['tower_level']:
            chars.add((entry['tower_level'],tuple(entry['character'])))
    return sorted(chars)


def audit():
    checked = 0
    for p in (2,3):
        for s,e in product(range(1,4),repeat=2):
            order = p**s
            for c in range(order):
                for extra in range(p**min(e,s)):
                    data = dict(prime=p,level=s,hom_orders=[s],hom=[c],ext_orders=[e],ext=[extra])
                    result = normalize(data)
                    # The elementary Ext cell is one cochain modulo the coboundaries
                    # p^e*t. Enumerate those coboundaries at each actual stage.
                    for d in range(result['delay']+1):
                        target = p**(s+d)
                        attained = any(t*p**e % target == extra*p**d % target for t in range(target))
                        assert attained == (d == result['delay'])
                    h = result['tower_level']
                    if h:
                        assert any(u % p and (u*c-p**(s-h)) % order == 0 for u in range(order))
                    else:
                        assert c == 0
                    checked += 1
    # Independently identify characters by their actual kernels in C4 x C2 x C2.
    els = list(product(range(4),range(2),range(2)))
    by_kernel = {}
    for a,b,c in els[1:]:
        kernel = tuple(x for x in els if (a*x[0]+2*b*x[1]+2*c*x[2]) % 4 == 0)
        d = normalize(dict(prime=2,level=2,hom_orders=[2,1,1],hom=[a,2*b,2*c],ext_orders=[],ext=[]))
        by_kernel.setdefault(kernel,set()).add((d['tower_level'],tuple(d['character'])))
    assert all(len(v) == 1 for v in by_kernel.values())
    assert sorted(next(iter(v)) for v in by_kernel.values()) == towers(2,[2,1,1])
    visible = sum((2,0,0) not in k for k in by_kernel)
    assert len(by_kernel) == 11 and visible == 4
    return checked


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    parser.add_argument('--towers',nargs='+',type=int,metavar='N',help='prime followed by homology exponents')
    args = parser.parse_args()
    if args.towers is not None:
        p,*orders = args.towers
        if p < 2 or any(e < 1 for e in orders):
            parser.error('supply a prime followed by positive exponents')
        try:
            print(json.dumps(towers(p, orders)))
        except ValueError as error:
            parser.error(str(error))
    elif args.input:
        try:
            print(json.dumps(normalize(json.loads(args.input.read_text()))))
        except (KeyError,ValueError) as error:
            parser.error(str(error))
    else:
        print(f'{audit()} finite-coefficient invariants checked; four of eleven towers retain the pair Hopf.')
