"""Certify independent higher probe differences forced by a filled degree-five loop.

JSON: sphere_degree k>=2, count>=1, and either a stationary holes/word
query, a pairs/braid/word plat, or a generators/faces/word complement group.
A supplied finite permutation action uses the plat solver's right-action
convention. General group searches assume a genuine probe-complement group.
"""
from argparse import ArgumentParser
from itertools import count,permutations,product
import json
from math import isqrt
from pathlib import Path

from semistrict_surface_face_whitehead import polynomial
from semistrict_surface_history_group import reduced
from semistrict_surface_plat_probes import presentation,proofs,word_value
from semistrict_surface_trefoil_mixed import matrix,project,read


def bracket_certificate(sheets,k):
    # For each pair of orbit spheres use the same stem sphere as the outer
    # bracket letter. Read a separate integral coefficient for each pair.
    count = (len(sheets)-1)//2
    assert len(set(sheets))==len(sheets)==2*count+1
    monomials = [(sheets[0],)*(k-2)+(sheets[2*i+1],) for i in range(count)]
    rows = []
    for j in range(count):
        a,b = 2*j+1,2*j+2
        for _ in range(k-2):
            a,b = [0,a],[0,b]
        weight,terms = polynomial([(1,a),(-1,b)],sheets)
        assert weight==k-1
        rows.append([terms.get(m,0) for m in monomials])
    assert rows==[[int(i==j) for i in range(count)] for j in range(count)]
    return dict(old_degree=k+4,orbit=sheets,monomials=monomials,coefficients=rows)


def sphere_brackets(vector,parking,k):
    """A lift of a detected old 2-sphere may also use the new punctures."""
    if not vector or not any(vector) or any(type(v) is not int for v in [*vector,*parking]):
        raise ValueError('expected a nonzero integral old coefficient vector')
    if not parking or k<3:
        raise ValueError('sphere brackets need a parked probe and sphere degree at least three')
    pivot = next(i for i,v in enumerate(vector) if v)
    lifted = vector+parking
    letters = list(range(len(lifted)))
    new = letters[len(vector):]
    words = [(z,)*(k-2)+(pivot,) for z in new]
    rows = []
    for z in new:
        terms = []
        for i,m in enumerate(lifted):
            if m:
                tree = i
                for _ in range(k-2):
                    tree = [z,tree]
                terms.append((m,tree))
        _,values = polynomial(terms,letters)
        rows.append([values.get(w,0) for w in words])
    assert rows==[[vector[pivot]*int(i==j) for i in range(len(new))] for j in range(len(new))]
    return dict(old_degree=k+4,monomials=words,coefficients=rows)


def congruence_orbit(mat,length):
    # Infinity is outside all ping-pong intervals, so every distinct power
    # of a nontrivial mixed word sends it to a distinct rational point.
    for p in count(2):
        if any(p%j==0 for j in range(2,isqrt(p)+1)):
            continue
        orbit = [p]
        while len(orbit)<length:
            z = project(mat,orbit[-1],p)
            if z==orbit[0]:
                break
            orbit.append(z)
        if len(orbit)==length:
            return p,orbit


def group_orbit(rank,faces,w,length,supplied):
    def checked(maps):
        if len(maps)!=rank or not maps:
            raise ValueError('expected one permutation per generator')
        size = len(maps[0])
        identity = tuple(range(size))
        if not size or any(sorted(m)!=list(identity) for m in maps):
            raise ValueError('expected permutations on a common nonempty set')
        if any(word_value(r,maps,size)!=identity for r in faces):
            return None
        action = word_value(w,maps,size)
        for start in identity:
            orbit = [start]
            while len(orbit)<length and action[orbit[-1]]!=start:
                orbit.append(action[orbit[-1]])
            if len(orbit)==length:
                return dict(permutations=maps),orbit
        return None
    if supplied is not None:
        result = checked(supplied)
        if result is None:
            raise ValueError('action violates a relator or all word orbits are too short')
        return result
    if not w:
        return dict(raw_loop_null=True,rewrites=[]),[]
    positive = proofs(rank,faces,w)
    for degree in count(1):
        for maps in product(permutations(range(degree)),repeat=rank):
            result = checked(maps)
            if result:
                return result
            proof = next(positive,None)
            if proof is not None:
                return dict(raw_loop_null=True,rewrites=proof['rewrites']),[]


def solve(data):
    k = data['sphere_degree']
    if 'old_sphere' in data:
        return sphere_brackets(data['old_sphere'],data['parked_coefficients'],k)
    n = data['count']
    if type(n) is not int or n<1 or type(k) is not int or k<2:
        raise ValueError('expected positive count and sphere degree at least two')
    w = data['word']
    if 'holes' in data:
        mixed = read(data['holes'],w)
        if mixed['raw_fibre_null']:
            return dict(raw_loop_null=True)
        p,orbit = congruence_orbit(mixed['matrix'],2*n+1)
        cover = dict(prime=p,matrix=mixed['matrix'])
    else:
        if 'pairs' in data:
            rank,faces = data['pairs'],presentation(data['pairs'],data['braid'])
        else:
            rank,faces = data['generators'],data['faces']
        if type(rank) is not int or rank<0 or any(type(g) is not int or not 0<abs(g)<=rank
                for word in [*faces,w] for g in word):
            raise ValueError('expected signed generator indices in the supplied presentation')
        cover,orbit = group_orbit(rank,faces,reduced(w),2*n+1,data.get('permutations'))
        if not orbit:
            return cover
    return dict(cover=cover,**bracket_certificate(orbit,k))


def audit():
    w = [1,2,-1,-2]
    cases = 0
    for n in (1,2,4):
        for k in range(2,9):
            result = solve(dict(holes=2,word=w,count=n,sphere_degree=k))
            cover = result['cover']
            # Replay as actual letters on all orbit points rather than
            # iterating the precomputed product matrix.
            word = read(2,w)['trefoil_word']
            for source,target in zip(result['orbit'],result['orbit'][1:]):
                z = source
                for g in reversed(word):
                    z = project(matrix([g]),z,cover['prime'])
                assert z==target
            cases += 1
    for k in range(2,6):
        hopf = solve(dict(pairs=2,braid=[2,2],word=w,count=1,sphere_degree=k))
        assert hopf['raw_loop_null']
        trefoil = solve(dict(pairs=2,braid=[2,2,2],word=w,count=1,sphere_degree=k))
        assert len(trefoil['cover']['permutations'][0])==3
    cyclic = dict(generators=1,faces=[],word=[1],count=2,sphere_degree=4)
    assert solve(dict(cyclic,permutations=[[1,2,3,4,0]]))['orbit']==[0,1,2,3,4]
    try:
        solve(dict(cyclic,faces=[[1]],permutations=[[1,2,3,4,0]]))
    except ValueError as err:
        assert 'violates a relator' in str(err)
    else:
        raise AssertionError('incompatible finite action accepted')
    for k in range(3,9):
        for parking in ([0],[-5,2,0],[1,1,1,1]):
            sphere_brackets([0,-3,2],parking,k)
    print(f'Checked {cases} orbit matrices, 18 lifted sphere matrices, Hopf and trefoil controls in four degrees, and a five-sheet cyclic action.')


if __name__=='__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('input',type=Path,nargs='?')
    args = cli.parse_args()
    if args.input:
        print(json.dumps(solve(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
