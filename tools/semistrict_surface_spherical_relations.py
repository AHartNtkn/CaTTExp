"""Read the one-probe sphere-orbit count on a general serial probe movie.

Use movie_spine JSON or a finite embedded-core spine presentation with fields
generators and faces. Decides using spherical identities and finite central
extensions, without requiring a triangulated three-manifold as input.
"""
from argparse import ArgumentParser
from collections import deque
from itertools import count, permutations, product
import json
from pathlib import Path

from semistrict_surface_history_group import inv, reduced
from semistrict_surface_movie_spine import presentation


def cyclic(w):
    w = reduced(w)
    while len(w)>1 and w[0]==-w[-1]:
        w = w[1:-1]
    if not w:
        return ()
    return min(s[i:]+s[:i] for s in (w,inv(w)) for i in range(len(s)))


def simplify(rank,faces):
    names = set(range(1,rank+1))
    spheres = 0
    while True:
        kept = {}
        for word in map(cyclic,faces):
            if not word or word in kept:
                spheres += 1
            else:
                kept[word] = None
        faces = sorted(kept,key=lambda w:(len(w),w))
        choice = next(((row,i,g) for row,w in enumerate(faces) for i,g in enumerate(w)
                       if w.count(g)+w.count(-g)==1),None)
        if choice is None:
            break
        row,i,g = choice
        w = faces.pop(row)
        expression = w[i+1:]+w[:i]
        if g>0:
            expression = inv(expression)
        names.remove(abs(g))
        faces = [reduced(tuple(x for a in rel for x in
                               (expression if a==abs(g) else inv(expression) if a==-abs(g) else (a,))))
                 for rel in faces]
    label = {g:i+1 for i,g in enumerate(sorted(names))}
    return len(names),[tuple(label[abs(g)]*(1 if g>0 else -1) for g in w) for w in faces],spheres


def insert(pivots,x):
    while x:
        i = x.bit_length()-1
        if i not in pivots:
            pivots[i] = x
            return True
        x ^= pivots[i]
    return False


def identities(rank,faces):
    # Conjugating the whole word, appending a disk, and conjugating back
    # permits a disk with any chosen stem. Breadth-first collisions enumerate
    # the parities of identities among these conjugates of the relators.
    moves = [('stem',g) for i in range(1,rank+1) for g in (i,-i)]
    moves += [('disk',g) for i in range(1,len(faces)+1) for g in (i,-i)]
    pending = deque([()])
    seen = {(): (0,None,None)}
    def trace(w):
        path = []
        while w:
            _,w,step = seen[w]
            path.append(step)
        return path[::-1]
    while pending:
        w = pending.popleft()
        for action,g in moves:
            step = (action,g)
            used = seen[w][0]
            if action=='stem':
                new = reduced((g,)+w+(-g,))
            else:
                face = faces[abs(g)-1]
                new = reduced(w+(face if g>0 else inv(face)))
                used ^= 1<<(abs(g)-1)
            if new in seen:
                mask = used^seen[new][0]
                if mask:
                    yield mask,dict(face_mask=mask,paths=[trace(w)+[step],trace(new)])
            else:
                seen[new] = (used,w,step)
                pending.append(new)
            yield 0,None
    while True:
        yield 0,None


def finite_tests(rank,faces):
    # In a finite regular permutation action a central involution is a
    # fixed-point-free flip. Enumerate its centralizer as signed permutations.
    for n in count(1):
        identity = tuple(range(2*n))
        flip = tuple(i^1 for i in identity)
        choices = [tuple(2*p[i//2]+((i%2)^bits[i//2]) for i in identity)
                   for p in permutations(range(n)) for bits in product((0,1),repeat=n)]
        inverses = {p:tuple(p.index(i) for i in identity) for p in choices}
        for maps in product(choices,repeat=rank):
            mask = 0
            for j,w in enumerate(faces):
                image = identity
                for g in w:
                    p = maps[g-1] if g>0 else inverses[maps[-g-1]]
                    image = tuple(p[i] for i in image)
                if image==flip:
                    mask |= 1<<j
                elif image!=identity:
                    break
            else:
                if mask:
                    yield mask,maps
            yield 0,()


def analyze(data):
    p = data if 'generators' in data else presentation(data)
    rank = p['generators']
    if type(rank) is not int or rank<0:
        raise ValueError('generator count must be nonnegative')
    faces = [tuple(w) for w in p['faces']]
    if any(type(g) is not int or not 0<abs(g)<=rank for w in faces for g in w):
        raise ValueError('a disk uses an unknown oriented edge')
    rank,faces,peeled = simplify(rank,faces)
    # Coboundaries are relator evaluations obtained by changing the signs
    # of the chosen lifts of individual generators.
    dual,positive = {},{}
    for i in range(1,rank+1):
        insert(dual,sum(((w.count(i)+w.count(-i))%2)<<j for j,w in enumerate(faces)))
    b1 = rank-len(dual)
    b2 = len(faces)-len(dual)+peeled
    if 'betti' in p and [1,b1,b2]!=p['betti']:
        raise ValueError('spine disagrees with the cut-and-tie homology')
    pos,neg = identities(rank,faces),finite_tests(rank,faces)
    spherical,certificates = [],[]
    while len(positive)+len(dual)<len(faces):
        mask,proof = next(pos)
        if mask and insert(positive,mask):
            spherical.append(proof)
            if len(positive)+len(dual)==len(faces):
                break
        mask,maps = next(neg)
        if mask and insert(dual,mask):
            certificates.append(dict(face_mask=mask,edge_permutations=maps))
    r = peeled+len(positive)
    return dict(generators=rank,faces=faces,split_off_spheres=peeled,betti=[1,b1,b2],
                spherical_identities=spherical,finite_tests=certificates,sphere_orbits=r,
                one_probe_aspherical=(r==0),pure_one_probe_higher_faithful=(b1==0 or r==0))


def pocket(word):
    split,merge = (1,'F'),(1,'M')
    p,site = (2,'p'),(2,'H')
    portal = [(0,'J')]
    inside = [split,p,site,merge]
    pocket = [split,p,merge]
    pair = [(0,'b'),(0,'c')]
    def chart(diagram,slot,source,target):
        return dict(diagram=diagram,slot=slot,input=source,output=target)
    return dict(vertex='x',path='aa',edges={'a':['x','x']},
                gates=dict(J=['x','aa','aa'],F=['x','a','aa'],M=['x','aa','a'],
                           **{g:['x','',''] for g in ('p','b','c','H')}),
                charts=[chart(portal,0,[],pocket),chart(inside,2,[],pair),
                        chart(inside,2,pair,[]),chart(portal,0,pocket,[])],
                seams=[[],word,[]],placement=[1,1,2])


def audit(compare_cores):
    from semistrict_surface_event_holes import nested,plat

    def verify(result):
        faces = result['faces']
        for proof in result['spherical_identities']:
            ends = []
            mask = 0
            for path in proof['paths']:
                w = ()
                for action,g in path:
                    if action=='stem':
                        w = reduced((g,)+w+(-g,))
                    else:
                        face = faces[abs(g)-1]
                        w = reduced(w+(face if g>0 else inv(face)))
                        mask ^= 1<<(abs(g)-1)
                ends.append(w)
            assert ends[0]==ends[1] and mask==proof['face_mask']
        for proof in result['finite_tests']:
            images = proof['edge_permutations']
            mask = 0
            for j,w in enumerate(faces):
                values = []
                for x in range(len(images[0])):
                    for g in w:
                        perm = images[abs(g)-1]
                        assert perm[x^1]==(perm[x]^1)
                        x = perm[x] if g>0 else perm.index(x)
                    values.append(x)
                bit = values[0]
                assert bit in (0,1) and all(y==(x^bit) for x,y in enumerate(values))
                mask |= bit<<j
            assert mask==proof['face_mask']

    for word,r in [([],1),([2,-2],1),([-2,2],1),([2,2],0),([-2,-2],0)]:
        result = analyze(pocket(word))
        verify(result)
        assert result['betti']==[1,2,1] and result['sphere_orbits']==r
    data = nested()
    for position in data['probes']:
        result = analyze(dict(data,placement=position))
        assert result['betti']==[1,0,1] and result['sphere_orbits']==1
    # Torus plus a redundant commutator disk. Its spherical identity uses
    # two copies of the first disk, while that disk also has a finite dual.
    result = analyze(dict(generators=2,faces=[[1,2,-1,-2],[1,1,2,-1,-1,-2]]))
    assert result['sphere_orbits']==1 and result['split_off_spheres']==0
    assert result['spherical_identities'] and result['finite_tests']
    verify(result)
    print('five wired pockets, three nested faces, and both kinds of certificates checked')
    if compare_cores:
        from semistrict_surface_splitting_spheres import analyze as normal
        checked = 0
        for length in range(4):
            for word in product((1,-1,2,-2,3,-3),repeat=length):
                answer = analyze(plat(word)[0])
                core = normal(dict(pairs=2,long=False,braid=word))
                for key in ('betti','sphere_orbits'):
                    assert answer[key]==core[key],(word,key)
                verify(answer)
                checked += 1
        print(f'{checked} signed four-strand movies agree with independent normal-sphere counts')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--compare-cores',action='store_true',help='cross-check signed plats using Regina')
    args = parser.parse_args()
    if args.input:
        print(json.dumps(analyze(json.loads(args.input.read_text())),indent=2))
    else:
        audit(args.compare_cores)
