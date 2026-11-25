"""Place a stationary punctured-disk probe query inside a closed trefoil plat.

The selected punctures occupy the first slots between the prefix and suffix.
Words have signed one-based meridian indices. --braids emits both actual seams.
"""
from argparse import ArgumentParser
from itertools import product
import json
from math import gcd,isqrt

from semistrict_surface_chain_probe import transport
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import inv,reduced
from semistrict_surface_plat_probes import presentation


def seams(holes):
    if holes<0:
        raise ValueError('negative puncture count')
    count = max(1,holes)
    sizes = [1,1]+[2]*count
    motions = []
    for i in range(1,holes):
        # Carry a balanced pair next to strand a, wind the entire pair,
        # then restore its slot. Each pair has trivial total peripheral.
        approach = tuple(-j for j in range(i+2,1,-1))
        motions.extend(cable(approach+(1,)*(10*i)+inv(approach),sizes))
    order = list(range(2*count+2))
    for i in range(holes):
        j = order.index(2+2*i)
        motions.extend(-k for k in range(j,i,-1))
        order.insert(i,order.pop(j))
    prefix = tuple(motions)
    # Bring the last b-side endpoint into the fourth slot, keeping it
    # unchanged. The residual closing pairs join successive b-bridges.
    base = tuple(-k for k in range(2*count+1,3,-1))+(2,2,2)
    return count+1,prefix,inv(prefix)+base,base


def substitute(word,images):
    return reduced(tuple(a for g in word for a in (images[g-1] if g>0 else inv(images[-g-1]))))


def multiply(x,y):
    a,b,c,d = x
    e,f,g,h = y
    return a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h


def matrix(word):
    # a translates by 1; b sends z to z/(1+z).
    frame = {1:(1,1,0,1),2:(1,0,1,1),-1:(1,-1,0,1),-2:(1,0,-1,1)}
    result = (1,0,0,1)
    for g in word:
        result = multiply(result,frame[g])
    return result


def scalar_matrix(m):
    return m in ((1,0,0,1),(-1,0,0,-1))


def project(m,z,p):
    a,b,c,d = m
    numerator,denominator = (a,c) if z==p else (a*z+b,c*z+d)
    return numerator*pow(denominator,-1,p)%p if denominator%p else p


def finite_certificate(mat):
    a,b,c,d = mat
    divisor = gcd(b,c,a-d)
    if not divisor:
        return None
    p = 2
    while divisor%p==0 or any(p%j==0 for j in range(2,isqrt(p)+1)):
        p += 1
    sheet = next(z for z in (0,1,p) if project(mat,z,p)!=z)
    return dict(prime=p,infinity=p,start=sheet,end=project(mat,sheet,p))


def read(holes,word,show_braids=False):
    if any(not 0<abs(g)<=holes for g in word):
        raise ValueError('word uses a meridian outside the marked disk')
    pairs,prefix,suffix,base = seams(holes)
    bottom = [(1,),(-1,)]+[(g,) for _ in range(pairs-1) for g in (2,-2)]
    middle = transport(bottom,prefix)
    selected = middle[:holes]
    assert selected==[(-1,)*(5*i)+(2,)+(1,)*(5*i) for i in range(holes)]
    assert transport(middle,suffix)==transport(bottom,base)
    relations = presentation(pairs,base)
    labels = [(1,)]+[(2,)]*(pairs-1)
    assert all(scalar_matrix(matrix(substitute(r,labels))) for r in relations)
    image = substitute(word,selected)
    mat = matrix(image)
    assert scalar_matrix(mat)==(not reduced(word))
    out = dict(pairs=pairs,selected_meridians=selected,trefoil_word=image,
               matrix=mat,raw_fibre_null=scalar_matrix(mat),finite_action=finite_certificate(mat))
    if show_braids:
        out.update(prefix=prefix,suffix=suffix)
    return out


def audit():
    from semistrict_surface_plat_probes import word_value
    from semistrict_surface_spherical_relations import simplify
    from itertools import permutations
    probes = 0
    for holes in range(7):
        pairs,_,_,base = seams(holes)
        rank,rels,_ = simplify(pairs,presentation(pairs,base))
        identity = (0,1,2)
        assert rank==2
        assert sum(all(word_value(r,p,3)==identity for r in rels)
                   for p in product(permutations(identity),repeat=2))==12
        w = (1,) if holes else ()
        for g in range(2,holes+1):
            w = reduced(w+(g,)+inv(w)+(-g,))
        result = read(holes,w)
        assert result['raw_fibre_null']==(holes==0)
        if holes>=2:
            assert all(sum(1 if x>0 else -1 for x in w if abs(x)==g)==0 for g in range(1,holes+1))
            assert all(not reduced(tuple(x for x in w if abs(x)!=g)) for g in range(1,holes+1))
        cert = result['finite_action']
        if cert:
            # Replay on just the p+1 sheets, letter by letter. Matrix
            # products act on a column starting with the rightmost letter.
            p = cert['prime']
            def act(word,z):
                for g in reversed(word):
                    z = project(matrix([g]),z,p)
                return z
            assert act(result['trefoil_word'],cert['start'])==cert['end']!=cert['start']
            for r in presentation(pairs,base):
                word = substitute(r,[(1,)]+[(2,)]*(pairs-1))
                assert all(act(word,z)==z for z in range(p+1))
        for length in range(4):
            for word in product([s*g for g in range(1,holes+1) for s in (1,-1)],repeat=length):
                assert scalar_matrix(matrix(substitute(word,result['selected_meridians'])))==(not reduced(word))
                probes += 1
    print(f'Checked seven stabilized trefoils, {probes} middle-disk words and Brunnian commutators through six punctures.')


def check_knots():
    from semistrict_surface_splitting_spheres import plat_link
    expected = plat_link(2,(2,2,2),False).sig(False,True)
    for holes in range(7):
        pairs,prefix,suffix,_ = seams(holes)
        knot = plat_link(pairs,prefix+suffix,False)
        crossings = knot.size()
        knot.simplify()
        assert knot.size()==3 and knot.sig(False,True)==expected
        print(f'{holes} punctures, {crossings} crossings simplify to {expected}')


if __name__=='__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('--holes',type=int)
    cli.add_argument('--word',type=int,nargs='*',default=[])
    cli.add_argument('--braids',action='store_true')
    cli.add_argument('--check-knots',action='store_true',help='also replay link simplification with Regina')
    args = cli.parse_args()
    if args.holes is None:
        audit()
    else:
        print(json.dumps(read(args.holes,args.word,args.braids),indent=2))
    if args.check_knots:
        check_knots()
