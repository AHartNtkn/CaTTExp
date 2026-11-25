"""Construct bounded degree-five tests for a fixed finite primary bottom group.

JSON keys bottom, middle, quadratic and face follow four_complex_operations.
--rank-two n enumerates inequivalent characters for two cyclic summands of
order n under bottom basis changes and output units (one representative each).
--bottom n1 n2 ... --index i constructs the quadratic table for character i.
"""
import json
from argparse import ArgumentParser
from itertools import combinations_with_replacement, product
from math import gcd, isqrt, prod
from pathlib import Path

from semistrict_surface_divisible_squares import diagonalize
from semistrict_surface_four_complex_operations import operation_presentation
from semistrict_surface_quadratic_image import reduction


def primary(bottom):
    if not bottom or any(type(n) is not int or n < 2 for n in bottom):
        raise ValueError('use a nonempty list of finite primary bottom orders')
    n = max(bottom)
    p = next((t for t in range(2,1+isqrt(n)) if n % t == 0),n)
    for value in bottom:
        while value % p == 0:
            value //= p
        if value != 1:
            raise ValueError('bottom orders must be powers of the same prime')
    return p,n


def reading_map(bottom, size, char):
    p,n = primary(bottom)
    target = ([2] if p == 2 else []) + list(bottom)
    first = 0 if p == 2 else 1
    result = []
    for j in range(size):
        values = [char[(k+first)*size+j] for k in range(len(target))]
        assert all(c % (n//m) == 0 for c,m in zip(values,target))
        result.append([c//(n//m) for c,m in zip(values,target)])
    return target,result


def tautological_pairing(bottom, target):
    p,n = primary(bottom)
    size = len(target)
    pairing = [0]*((len(bottom)+1)*size)
    if p == 2:
        pairing[0] = n//2
    for i,m in enumerate(bottom):
        pairing[(i+1)*size+i+int(p == 2)] = n//m
    return pairing


def tester(bottom, index):
    p,n = primary(bottom)
    middle = [(m*(2 if p == 2 else 1) if i == j else gcd(m,k))
              for (i,m),(j,k) in combinations_with_replacement(enumerate(bottom),2)]
    size = len(middle)
    universal_q = [[int(i == j) for j in range(size)] for i in range(size)]
    rows,_,_ = operation_presentation(bottom,middle,universal_q)
    width = (len(bottom)+1)*size
    diag,change,used = diagonalize(rows,0,width)
    assert used == width
    orders = [gcd(n,diag[j][j]) for j in range(width)]
    number = prod(orders)
    if index < 0 or index >= number:
        raise ValueError(f'index must be between zero and {number-1}')
    digits = []
    for m in orders:
        index,digit = divmod(index,m)
        digits.append(digit*(n//m))
    char = [sum(x*y for x,y in zip(row,digits)) % n for row in change]
    target,q = reading_map(bottom,size,char)
    new_rows,_,_ = operation_presentation(bottom,target,q)
    pairing = tautological_pairing(bottom,target)
    assert all(sum(x*y for x,y in zip(row,pairing)) % n == 0 for row in new_rows)
    return dict(number_of_characters=number,middle_orders=target,quadratic=q,
                operation_readings=pairing,character_modulus=n,cyclic_top_bound=n if p != 2 else 2*n)


def compress(bottom,middle,quadratic,face):
    p,n = primary(bottom)
    rows,gens,_ = operation_presentation(bottom,middle,quadratic)
    r,s = len(bottom),len(middle)
    if len(face) != r+1 or any(len(row) != s or any(type(c) is not int for c in row) for row in face):
        raise ValueError('face needs integral eta and bracket rows')
    flat = [c for row in face for c in row]
    width = len(flat)
    if reduction(rows+gens,width)[1](flat) != 1:
        return {'outside_bottom_image':True}
    diag,change,used = diagonalize(rows,0,width)
    assert used == width
    for col in range(width):
        order = gcd(n,diag[col][col])
        char = [v[col]*(n//order) % n for v in change]
        value = sum(x*y for x,y in zip(flat,char)) % n
        if value:
            break
    else:
        return {'outside_bottom_image':False,'raw_order':1}
    assert all(sum(x*y for x,y in zip(row,char)) % n == 0 for row in rows)
    target,middle_map = reading_map(bottom,s,char)
    def send(v):
        return [sum(c*row[j] for c,row in zip(v,middle_map)) % m for j,m in enumerate(target)]
    new_q = [send(v) for v in quadratic]
    new_face = [send(v) for v in face]
    new_rows,_,_ = operation_presentation(bottom,target,new_q)
    pairing = tautological_pairing(bottom,target)
    assert all(sum(x*y for x,y in zip(row,pairing)) % n == 0 for row in new_rows)
    assert sum(x*y for x,y in zip([c for row in new_face for c in row],pairing)) % n == value
    return dict(outside_bottom_image=False,raw_order=reduction(rows,width)[1](flat),
                middle_orders=target,middle_map=middle_map,quadratic=new_q,face=new_face,
                character_value=value,character_modulus=n,cyclic_top_bound=n if p != 2 else 2*n)


def rank_two(n):
    p,_ = primary([n])
    parity = 2 if p == 2 else 1
    unseen = set(product(range(parity),range(parity),range(parity),range(n),range(n)))
    unseen.discard((0,0,0,0,0))
    # Elementary basis changes generate GL2 over the local ring. Swapping and
    # transvection generate elementary matrices; diagonal units supply det.
    units = [v for v in range(1,n) if gcd(v,n) == 1]
    matrices = [(0,1,1,0),(1,1,0,1)]+[(v,0,0,1) for v in units]
    reps = []
    while unseen:
        seed = min(unseen)
        unseen.remove(seed)
        stack = [seed]
        count = 0
        while stack:
            x,h,y,u,v = stack.pop()
            count += 1
            images = [(x,h,y,w*u % n,w*v % n) for w in units]
            for a,b,c,d in matrices:
                det = a*d-b*c
                images.append(((a*a*x+a*b*h+b*b*y) % parity,det*h % parity,
                               (c*c*x+c*d*h+d*d*y) % parity,
                               det*(a*u-b*v) % n,det*(-c*u+d*v) % n))
            for other in images:
                if other in unseen:
                    unseen.remove(other)
                    stack.append(other)
        reps.append(dict(character=seed,size=count))
    return reps


def audit():
    from semistrict_surface_four_complex_operations import solve
    count = 0
    cases = [([2,4],[8,2,4],[[2,0,0],[0,1,0],[0,0,1]]),
             ([3,9],[3,9,0],[[1,0,0],[0,3,0],[0,1,0]]),
             ([4,4],[8,4,8],[[1,0,0],[0,1,0],[0,0,1]]),
             ([8,8],[16,8,16],[[1,0,0],[0,1,0],[0,0,1]])]
    for a,b,q in cases:
        for coeffs in product((-1,0,1),repeat=4):
            face = [[coeffs[0]*v for v in q[0]],
                    [coeffs[1]*v+coeffs[2]*w for v,w in zip(q[0],q[1])],
                    [coeffs[3]*v for v in q[2]]]
            data = compress(a,b,q,face)
            expected = solve(a,b,q,face)
            assert not data['outside_bottom_image'] and data['raw_order'] == expected['raw_order']
            if data['raw_order'] != 1:
                target = solve(a,data['middle_orders'],data['quadratic'],data['face'])
                assert target['in_bottom'] and target['raw_order'] > 1
            count += 1
    assert compress([2],[0],[[0]],[[1],[0]]) == {'outside_bottom_image':True}
    for n in (2,4,8,3,9,5,25):
        reps = rank_two(n)
        assert sum(r['size'] for r in reps) == ((8 if n % 2 == 0 else 1)*n*n-1)
        if n % 2:
            assert all(r['character'][:3] == (0,0,0) and r['character'][3] == 0 for r in reps)
            assert {n//gcd(n,r['character'][4]) for r in reps} == {d for d in range(2,n+1) if n % d == 0}
    # Compute independent orbit images from the three actual quadratic values
    # and their five operation readings, using every invertible basis at n=4.
    n = 4
    all_images = set()
    for rep in rank_two(n):
        x,h,y,u,v = rep['character']
        hopf = (x,h,y)
        tx = (0,u,2*h-v)
        ty = (2*h-u,v,0)
        images = set()
        def dot(row,col):
            return sum(i*j for i,j in zip(row,col))
        for a,b,c,d in product(range(n),repeat=4):
            if gcd(a*d-b*c,n) != 1:
                continue
            qx,qy = (a*a,a*b,b*b),(c*c,c*d,d*d)
            polar = (2*a*c,a*d+b*c,2*b*d)
            for w in (1,3):
                images.add((dot(hopf,qx)%2,dot(hopf,polar)%2,dot(hopf,qy)%2,
                            w*(a*dot(tx,polar)+b*dot(ty,polar))%n,
                            w*(c*dot(tx,polar)+d*dot(ty,polar))%n))
        assert min(images) == rep['character'] and len(images) == rep['size']
        assert all_images.isdisjoint(images)
        all_images.update(images)
    assert len(all_images) == 127
    for a,number in (([2,4],32),([4,4],128),([3,9],9),([3,3,3],6561)):
        assert tester(a,0)['number_of_characters'] == number
        assert any(any(row) for row in tester(a,number-1)['quadratic'])
        if number <= 128:
            assert len({tuple(map(tuple,tester(a,i)['quadratic'])) for i in range(number)}) == number
    for p,a in ((3,3),(5,2),(7,1)):
        n = p**a
        for b in range(1,a+1):
            k = p**(a-b)
            q = [[0,-k],[k,0],[0,0]]
            data = solve([n,n],[n,n],q,[[0,0],[p**(b-1)*k,0],[0,0]])
            assert data['bottom_image'] == [p**b] and data['raw_order'] == p
    return count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('input',nargs='?',type=Path)
    mode.add_argument('--rank-two',type=int)
    mode.add_argument('--bottom',nargs='+',type=int)
    parser.add_argument('--index',type=int)
    args = parser.parse_args()
    try:
        if args.index is not None and not args.bottom:
            parser.error('--index needs --bottom')
        if args.bottom:
            print(json.dumps(tester(args.bottom,args.index or 0)))
        elif args.input:
            print(json.dumps(compress(**json.loads(args.input.read_text()))))
        elif args.rank_two is not None:
            reps = rank_two(args.rank_two)
            print(json.dumps(dict(number=len(reps),orbits=reps)))
        else:
            print(f'{audit()} integral source comparisons checked through the bounded middle assignments.')
    except (TypeError,ValueError) as error:
        parser.error(str(error))
