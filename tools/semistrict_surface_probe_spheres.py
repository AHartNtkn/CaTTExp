"""Decide spherical identities on residually finite two-dimensional spines.

For a general 2-spine give generators (a count), faces (one signed boundary
word per 2-cell), and disks (triples [stem, one-based face, orientation]).
For an exterior sphere and its translates on a closed plat, give pairs, braid,
word and sphere_degree >= 2. All group letters are signed and one-based.
"""
from argparse import ArgumentParser
from collections import Counter
from itertools import count, permutations, product
import json
from pathlib import Path

from semistrict_surface_component_braids import Partition
from semistrict_surface_face_whitehead import polynomial
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_plat_probes import presentation, proofs, rewrites, word_value


def coordinates(disks, address):
    values = Counter()
    for stem,face,sign in disks:
        values[address(stem),face] += sign
    return {key:n for key,n in values.items() if n}


def finite_readings(rank,faces,disks):
    for degree in count(1):
        identity = tuple(range(degree))
        for maps in product(permutations(identity),repeat=rank):
            if all(word_value(r,maps,degree)==identity for r in faces):
                values = coordinates(disks,lambda stem:word_value(stem,maps,degree)[0])
                if values:
                    yield dict(null=False,sheets=degree,permutations=maps,
                               coefficients=[[a,f,n] for (a,f),n in sorted(values.items())])
            yield None


def sphere(data):
    rank = data['generators']
    if type(rank) is not int or rank<0:
        raise ValueError('give a nonnegative generator count')
    def checked(word):
        if any(type(x) is not int or not 0<abs(x)<=rank for x in word):
            raise ValueError('unknown oriented 1-cell')
        return tuple(word)
    faces = [checked(w) for w in data['faces']]
    disks = []
    boundary = ()
    for stem,face,sign in data['disks']:
        stem = reduced(checked(stem))
        if type(face) is not int or not 1<=face<=len(faces) or type(sign) is not int or sign not in (-1,1):
            raise ValueError('give a valid 2-cell and orientation')
        rel = faces[face-1]
        boundary = reduced(boundary+stem+(rel if sign>0 else inv(rel))+inv(stem))
        disks.append((stem,face,sign))
    if boundary:
        raise ValueError('the based disk boundaries do not cap in the free 1-skeleton')
    partition = Partition()
    verified = []
    searches = []
    for i,(a,f,s) in enumerate(disks):
        for b,g,t in disks[:i]:
            if f==g and t==-s and a!=b:
                searches.append((a,b,proofs(rank,faces,reduced(a+inv(b)))))
    covers = finite_readings(rank,faces,disks)
    while coordinates(disks,partition.at):
        answer = next(covers)
        if answer:
            return answer
        for a,b,search in searches:
            if partition.at(a)==partition.at(b):
                continue
            proof = next(search,None)
            if proof is not None:
                partition.unite(a,b)
                verified.append(dict(left=a,right=b,rewrites=proof['rewrites']))
    return dict(null=True,stem_equalities=verified)


def plat(data):
    degree = data['sphere_degree']
    if type(degree) is not int or degree<2:
        raise ValueError('expected a sphere degree of at least two')
    rank = data['pairs']
    faces = presentation(rank,data['braid'])
    infinity = len(faces)+1
    word = tuple(data['word'])
    # Only the distinguished sphere over infinity is being queried. The
    # other relators present the deck group; their 2-cells are never used.
    result = sphere(dict(generators=rank,faces=[*faces,()],
                         disks=[[word,infinity,1],[[],infinity,-1]]))
    if not result['null']:
        maps = result['permutations']
        sheet = word_value(word,maps,result['sheets'])[0]
        a,b = 1,0
        for _ in range(degree-2):
            a,b = [0,a],[0,b]
        _,values = polynomial([(1,a),(-1,b)],[0,sheet])
        monomial = (0,)*(degree-2)+(sheet,)
        assert values[monomial]==1
        result.update(tensor_word=monomial,coefficient=values[monomial])
    result['raw_degree'] = degree+4
    return result


def audit():
    # A genuine identity using a nonempty face, plus its inverse, with one
    # stem changed by that face boundary. Every coefficient cancels upstairs.
    face = (1,2,-1,-2)
    data = dict(generators=2,faces=[face],disks=[[[],1,1],[face,1,-1]])
    positive = sphere(data)
    assert positive['null'] and positive['stem_equalities']
    for proof in positive['stem_equalities']:
        word = reduced(proof['left']+inv(proof['right']))
        for p,a,b in proof['rewrites']:
            assert (a,b) in rewrites(2,[face]) and word[p:p+len(a)]==a
            word = word[:p]+b+word[p+len(a):]
        assert not word
    # The boundary of the lifted commutator cube in the 2-skeleton of the
    # three-torus. Its six based squares give a sphere with zero augmentation.
    # Two reductions of 321 to 123 by adjacent switches use the three faces.
    faces = [(i,j,-i,-j) for i,j in [(3,2),(3,1),(2,1)]]
    left = [((),1,1),((2,),2,1),((),3,1)]
    right = [((3,),3,1),((),2,1),((1,),1,1)]
    disks = left+[(w,f,-s) for w,f,s in reversed(right)]
    result = sphere(dict(generators=3,faces=faces,disks=disks))
    assert not result['null'] and result['sheets']==2
    assert not coordinates(disks,lambda w:0)
    maps = result['permutations']
    assert all(word_value(f,maps,2)==(0,1) for f in faces)
    assert result['coefficients']==[[a,f,n] for (a,f),n in sorted(
        coordinates(disks,lambda w:word_value(w,maps,2)[0]).items())]
    try:
        sphere(dict(generators=3,faces=faces,disks=disks[:-1]))
    except ValueError as err:
        assert 'do not cap' in str(err)
    else:
        raise AssertionError('an uncapped boundary was accepted')
    print('six based squares cap, have zero unlifted coefficients, and survive on two sheets')
    for k in range(2,10):
        for twists,vanishes in [(1,True),(2,True),(3,False),(-3,False)]:
            data = dict(pairs=2,braid=[2 if twists>0 else -2]*abs(twists),
                        word=[1,2,-1,-2],sphere_degree=k)
            result = plat(data)
            assert result['null']==vanishes and result['raw_degree']==k+4
            if not vanishes:
                assert result['sheets']==3 and result['coefficient']==1
    print('32 closed-plat queries in raw degrees 6 through 13; all nonzero commutator classes survive on three sheets')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        print(json.dumps(plat(data) if 'pairs' in data else sphere(data),indent=2))
    else:
        audit()
