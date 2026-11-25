"""Read stable coefficients of probe brackets, including finite-order classes.

A sphere query gives target_sphere, source_sphere and coordinates on the
indicated Hilton sphere. A word query gives terms [[c,[letters]],...],
one common word length, modulus (0 means integers), parked and brackets.
"""
from argparse import ArgumentParser
from collections import Counter
import json
from pathlib import Path


def value(c,order):
    return c%order if order else c


def factor(d,k,coords):
    if not 2<=d<=k or k>7 and (d,k)!=(4,8):
        raise ValueError('supported sphere factors have 2 <= d <= k <= 7, and (4,8)')
    if len(coords)!=(2 if (d,k) in [(4,7),(4,8)] else 1) or any(type(a) is not int for a in coords):
        raise ValueError('incorrect coordinates for the sphere factor')
    # For k>=3 take the inverse of the Hopf fibre isomorphism first at d=2.
    base = 3 if d==2 and k>=3 else d
    if (base,k)==(4,8):
        orders = [2,2]
        channels = [('stable second James-Hopf invariant',2,coords[0])]
    elif (base,k)==(4,7):
        orders = [0,12]
        channels = [('Hopf invariant',0,coords[0]),('stabilization',24,coords[0]+2*coords[1])]
    elif (base,k)==(3,7):
        orders = [2]
        channels = [('stable second James-Hopf invariant',2,coords[0])]
    elif (base,k)==(3,6):
        orders = [12]
        channels = [('stabilization',24,2*coords[0])]
    else:
        orders = [[0,2,2,24][k-base]]
        channels = [('stabilization',orders[0],coords[0])]
    readings = [(name,order,value(c,order)) for name,order,c in channels]
    return dict(through_complex_hopf=base!=d,source_orders=orders,
                nonzero=any(value(a,n) for a,n in zip(coords,orders)),
                stable_adjoint_detected=any(c for _,_,c in readings),readings=readings)


def bracket(terms,modulus,z,steps):
    if type(steps) is not int or steps<1 or type(modulus) is not int or modulus<0:
        raise ValueError('expected positive bracket count and a nonnegative modulus')
    if not terms or not terms[0][1]:
        raise ValueError('expected a positive word length')
    size = len(terms[0][1])
    coefficients = Counter()
    for c,word in terms:
        if len(word)!=size or type(c) is not int:
            raise ValueError('terms must lie in one word-length summand with integer coordinates')
        coefficients[tuple(word)] += c
    old = {w:value(c,modulus) for w,c in coefficients.items() if z not in w and value(c,modulus)}
    if not old:
        raise ValueError('the old projection has zero coefficient')
    for _ in range(steps):
        new = Counter()
        for w,c in coefficients.items():
            # Coefficients are written on the right. Passing the coefficient
            # through z cancels its degree in the Samelson commutator sign.
            new[(z,)+w] += c
            new[w+(z,)] -= (-1)**len(w)*c
        coefficients = {w:value(c,modulus) for w,c in new.items() if value(c,modulus)}
    recovered = {w:coefficients.get((z,)*steps+w,0) for w in old}
    assert recovered==old
    return [[[z]*steps+list(w),c] for w,c in recovered.items()]


def solve(data):
    if 'target_sphere' in data:
        return factor(data['target_sphere'],data['source_sphere'],data['coordinates'])
    return bracket(data['terms'],data['modulus'],data['parked'],data['brackets'])


def audit():
    total = 0
    for k in range(2,8):
        for d in range(2,k+1):
            if (k,d)==(7,4):
                inputs = [[a,b] for a in (-24,-2,0,1,24) for b in range(12)]
            else:
                inputs = [[i] for i in range(-24,25)]
            for coords in inputs:
                report = factor(d,k,coords)
                assert report['stable_adjoint_detected']==report['nonzero']
                total += 1
    assert factor(4,8,[1,0])['stable_adjoint_detected']
    hidden = factor(4,8,[0,1])
    assert hidden['nonzero'] and not hidden['stable_adjoint_detected']
    # For the two letters use a genuine reduced commutator on the old
    # part, with another term that disappears after forgetting z.
    from semistrict_surface_face_whitehead import polynomial
    _,comm = polynomial([(1,[0,1])],['a','b'])
    tests = 0
    for order in (0,2,24):
        for c in ([1,-3] if order!=24 else [2,8,12]):
            terms = [[v*c,list(w)] for w,v in comm.items()]+[[3,['a','z']],[-7,['z','z']]]
            for steps in range(1,9):
                readings = bracket(terms,order,'z',steps)
                assert len(readings)==2 and all(n==value(c,order) for _,n in readings)
                tests += 1
    print(f'Checked {total} sphere-factor readings through dimension seven and {tests} iterated stable brackets, including the dimension-eight kernel control.')


if __name__=='__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('input',type=Path,nargs='?')
    args = cli.parse_args()
    if args.input:
        print(json.dumps(solve(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
