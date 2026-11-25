"""Transport a reversible binary comparison kernel along the top coefficient map.

JSON: homology and top are cyclic orders (0 means Z), evaluation has one top
vector per homology generator. kernel lists generators of the known universal
kernel in homology coordinates; face is optional. With lower="pair", supply
only top, evaluation and optional face, for P3(K(C2,2) wedge K(C2,2)).
"""
import json
from argparse import ArgumentParser
from collections import Counter
from itertools import product
from pathlib import Path

from semistrict_surface_four_complex_operations import subgroup
from semistrict_surface_quadratic_image import reduction


def image_rows(data):
    pair = data.get('lower') == 'pair'
    if 'lower' in data and not pair:
        raise ValueError('unknown lower type')
    source = [4,2,2] if pair else data['homology']
    kernel = [[2,0,0]] if pair else data['kernel']
    top, matrix = data['top'],data['evaluation']
    if any(type(n) is not int or n < 0 or n == 1 for n in [*source,*top]):
        raise ValueError('orders must be zero or at least two')
    def vector(v,width):
        if len(v) != width or any(type(x) is not int for x in v):
            raise ValueError('invalid coordinate vector')
    for row,n in zip(matrix,source,strict=True):
        vector(row,len(top))
        if any((c*n % m if m else c*n) for c,m in zip(row,top)):
            raise ValueError('evaluation violates a homology order')
    image = []
    for v in kernel:
        vector(v,len(source))
        image.append([sum(c*row[j] for c,row in zip(v,matrix)) for j in range(len(top))])
    orders = [[n*int(i == j) for j in range(len(top))] for i,n in enumerate(top) if n]
    return orders,image


def evaluate(data):
    orders,image = image_rows(data)
    top = data['top']
    pair = data.get('lower') == 'pair'
    parts = subgroup(orders,len(top),image)
    result = {'kernel_if_pair_fills' if pair else 'kernel_orders':parts}
    if pair:
        result['degree_reflection'] = 'equivalent_to_pair_nonfilling' if parts else 'yes'
    if 'face' in data:
        face = data['face']
        if len(face) != len(top) or any(type(x) is not int for x in face):
            raise ValueError('invalid face coordinates')
        inside = reduction(orders+image,len(top))[1](face) == 1
        if pair:
            zero = reduction(orders,len(top))[1](face) == 1
            result['fills'] = 'yes' if zero else 'equivalent_to_pair_filling' if inside else 'no'
        else:
            result['fills'] = inside
    return result


def pushout_checks():
    # Model the separating top map u:C->G. Compute the actual equivalence
    # classes of G x D under the antidiagonal and read D in that quotient.
    count = 0
    for c,g,d in product(range(2,10),repeat=3):
        for u,f in product(range(g),range(d)):
            if c*u % g or c*f % d:
                continue
            orbit = {(u*t % g, -f*t % d) for t in range(c)}
            kernel = [[t] for t in range(1,c) if u*t % g == 0]
            data = dict(homology=[c],top=[d],evaluation=[[f]],kernel=kernel)
            for v in range(d):
                assert evaluate(dict(data,face=[v]))['fills'] == ((0,v) in orbit)
                count += 1
    return count


def disk_checks():
    from catt import arr, comp2, infer, src, v
    from semistrict_surface_higher_winding import disk
    from semistrict_surface_mixed_winding import Reading, evaluate as read, slots
    cycle = {((0,i),(1,j)): (1 if i != j else -1) for i,j in product(range(2),repeat=2)}
    count = 0
    for rank,side in product((3,4),(False,True)):
        ctx,arc = disk(rank,side)
        face = src(ctx,arc)
        extended = ctx+(arr(infer(ctx,face),face,face),)
        # A repeated intrinsic slot in the actual term and an offset from the
        # naturality head. The incidence on the repeated input must be two.
        variable = v(len(ctx))
        term = comp2(extended,rank,comp2(extended,rank,variable,variable),arc)
        assert infer(extended,term) == infer(ctx,arc)
        _,at = slots(ctx)
        active = next(pos[:2] for pos in at if len(pos) == rank)
        for mass,charge in product((-1,1,2),(-2,1)):
            labels = [Reading(mass=mass if len(pos) == 2 and pos != active else 0,
                charge=charge if len(pos) == rank else 0) for pos in at]
            base = read(arc,labels,rank).edges
            assert any(base.values())
            for a in range(-3,4):
                reading = Reading(edges=Counter({e:a*c for e,c in cycle.items()}))
                actual = read(term,labels+[reading],rank).edges
                for b in range(-2,3):
                    other = Reading(edges=Counter({e:b*c for e,c in cycle.items()}))
                    other_value = read(term,labels+[other],rank).edges
                    # Product with C6 and quotient by (1,-2); these labels
                    # (a,0) and (b,2(a-b)) represent the same new top disk.
                    for edge,sign in cycle.items():
                        assert actual[edge] == base[edge]+2*a*sign
                        assert (2*actual[edge]-2*other_value[edge]-4*(a-b)*sign) % 6 == 0
                    count += 1
    return count


def audit():
    count = pushout_checks()
    disks = disk_checks()
    pairs = 0
    for s in range(1,7):
        n = 2**s
        for a,b,c in product(range(n),range(0,n,n//2),range(0,n,n//2)):
            if 4*a % n:
                continue
            for face in (0,n//2,1):
                data = dict(lower='pair',top=[n],evaluation=[[a],[b],[c]],face=[face])
                result = evaluate(data)
                expected = 'yes' if face == 0 else 'equivalent_to_pair_filling' if face == 2*a % n else 'no'
                assert result['fills'] == expected
                pairs += 1
    # A noncyclic coefficient and a free component, with a mixed generator.
    data = dict(homology=[4,0],top=[0,8],evaluation=[[0,2],[2,1]],kernel=[[1,1]])
    assert evaluate(dict(data,face=[4,6]))['fills']
    assert not evaluate(dict(data,face=[4,2]))['fills']
    return count,disks,pairs


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    args = parser.parse_args()
    if args.input:
        try:
            print(json.dumps(evaluate(json.loads(args.input.read_text()))))
        except (KeyError,TypeError,ValueError) as error:
            parser.error(str(error))
    else:
        print('%d balanced coefficient tests, %d labelled disk relabellings, %d pair-stage queries.' % audit())
