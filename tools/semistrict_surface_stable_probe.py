"""Read stable coefficients of probe brackets, including finite-order classes.

A sphere query gives target_sphere, source_sphere and coordinates on the
indicated Hilton sphere. For source_sphere 8, adams_index j requests a
propagation certificate in old degree 13+8j. A word query gives terms [[c,[letters]],...],
one common word length, modulus (0 means integers), parked and brackets.
"""
from argparse import ArgumentParser
from collections import Counter
import json
from pathlib import Path


def value(c,order):
    return c%order if order else c


def factor(d,k,coords):
    if not 2<=d<=k<=8:
        raise ValueError('supported sphere factors have 2 <= d <= k <= 8')
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
    elif (base,k)==(3,8):
        orders = [2]
        channels = [('stable second James-Hopf invariant',24,12*coords[0])]
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


def compose(*maps):
    """Read a typed composite from the target on the left to the source on the right."""
    for left,right in zip(maps,maps[1:]):
        if left[1]!=right[2]:
            raise ValueError(f'incompatible sphere dimensions for {left[0]} and {right[0]}')
    return dict(word=[name for name,_,_ in maps],source=maps[-1][1],target=maps[0][2])


def propagate(d,coords,j):
    if type(j) is not int or j<0:
        raise ValueError('adams_index must be a nonnegative integer')
    reading = factor(d,8,coords)
    shift = 8*j+1
    result = dict(old_degree=12+shift, factor=reading)
    if not reading['nonzero']:
        return dict(result,operation='zero coordinate')
    if reading['stable_adjoint_detected']:
        return dict(result,operation='park and bracket',brackets=shift)
    # Quaternionic connecting map reads the desuspension. H_2 then
    # substitutes eta_5 for nu_prime. mu on S^7 is itself a suspension.
    mu = ('mu',7+shift,7)
    fibre = compose(('nu_prime',6,3),('eta',7,6),mu)
    hopf = compose(('eta',6,5),('eta',7,6),mu)
    theta_stem = hopf['source']-hopf['target']-1  # eta*mu
    lift_degree = theta_stem+2
    ko_groups = ('Z','Z/2','Z/2','0','Z','0','0','0')
    # KO_*(C eta) = KU_* by Wood. Rational C eta has cells in 0 and 2.
    ko_theta = ko_groups[theta_stem%8]
    ko_lift = 'Z' if lift_degree%2==0 else '0'
    finite_lift_group = lift_degree not in (0,2)
    assert ko_theta=='Z/2' and ko_lift=='Z' and finite_lift_group
    return dict(result,operation='precompose',sphere_map=['mu',8+shift,8],
                quaternionic_boundary=fibre,james_hopf=hopf,
                cofiber_lift_degree=lift_degree,ko_of_theta=ko_theta,
                ko_of_cofiber=ko_lift,spherical_cofiber_image=0,
                required_collapsed_ko_class=coords[1]%2)


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
        if 'adams_index' in data:
            if data['source_sphere']!=8:
                raise ValueError('Adams propagation starts in sphere degree eight')
            return propagate(data['target_sphere'],data['coordinates'],data['adams_index'])
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
    routes = Counter()
    for d in range(2,9):
        inputs = ([[a,b] for a in range(2) for b in range(2)] if d==4 else
                  [[a] for a in range(24)] if d==5 else [[-1],[0],[1],[2]])
        for coords in inputs:
            for j in (0,1,2,15,1000):
                report = propagate(d,coords,j)
                op = report['operation']
                routes[op] += 1
                assert report['old_degree']==13+8*j
                if op=='precompose':
                    assert d==4 and coords==[0,1]
                    assert report['james_hopf']['source']==report['old_degree']-5
                    assert report['required_collapsed_ko_class']==1
                elif op=='park and bracket':
                    assert report['brackets']==report['old_degree']-12
                else:
                    assert all(value(c,n)==0 for c,n in zip(coords,report['factor']['source_orders']))
    assert routes['precompose']==5
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
    print('Dimension-eight propagation certificates:',dict(routes))


if __name__=='__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('input',type=Path,nargs='?')
    args = cli.parse_args()
    if args.input:
        print(json.dumps(solve(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
