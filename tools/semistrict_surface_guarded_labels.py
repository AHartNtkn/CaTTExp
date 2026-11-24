"""All-boundary degree-four reflection for braid-preserving mixed 4-rules.

Use the presentation format of semistrict_surface_invertible_updates. No query
is needed. The exact integer solver accepts abelian unary cycle groups.
Every crossing-free extra rule must be at one event on its own spatial path.
"""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import combinations, product
import json
from pathlib import Path

from semistrict_surface_braid_reflection import certify
from semistrict_surface_invertible_updates import Colours, Faces
from semistrict_surface_scalar_sites import coefficients
from semistrict_surface_shared_edge import braid_image


def separate(h, movie, cols):
    strands = list(range(len(h)))
    crosses, local = [], []
    values = [[0]*len(cols.axis) for _ in h]
    for token in movie:
        if isinstance(token,int):
            i = token-1
            strands[i:i+2] = strands[i:i+2][::-1]
            crosses.append(token)
        else:
            name,i,sign = token
            e = strands[i]
            local.append((name,e,sign))
            if name in cols.axis:
                values[e][cols.axis[name]] += sign
    return tuple(crosses),local,values


def solve(data):
    cols = Colours(data)
    for axes in cols.cycles.values():
        if any(frozenset(pair) not in cols.commutations for pair in combinations(axes,2)):
            raise ValueError('integer label solver needs commuting cycles in each colour')
    rows = defaultdict(list)
    guarded = []
    for index,entry in enumerate(data['attachments']):
        face = Faces(data,entry,cols)
        left,right = [separate(face.original,m,cols) for m in face.movies]
        n = len(face.history)
        if braid_image(n,left[0])!=braid_image(n,right[0]):
            raise ValueError('mixed rule changes its structural braid')
        delta = [tuple(b-a for a,b in zip(x,y)) for x,y in zip(left[2],right[2])]
        if not left[0]:
            if n!=1 or face.original[0][0]!=0 or tuple(data['rules'][face.original[0][1]][:2]) != (face.root,face.path):
                raise ValueError('crossing-free rule must act at one event on its own input path')
            rows[face.history[0][1]].append(delta[0])
        else:
            guarded.append((index,face,left,right,delta))
    cubes = []
    for index,face,left,right,delta in guarded:
        reversible = True
        for e,((_,c),d) in enumerate(zip(face.history,delta)):
            if coefficients(rows[c],d) is None:
                return dict(reflects=False, reason='crossing guard', attachment=index, occurrence=e,
                            witness=[face.root,face.path,face.original,left[1],right[1]])
            if coefficients(rows[c], tuple(-v for v in d)) is None:
                reversible = False
        if reversible and (left[0],right[0])==((2,1,2),(1,2,1)):
            cubes.append([face.root,face.path,face.history,left[0],right[0]])
    shapes = {c:data['rules'][c] for c in cols.cycles}
    missing = certify(dict(edges=data['edges'],rules=shapes,attachments=cubes))
    if missing is None:
        return dict(reflects=True)
    (a,b,c),(l,r) = missing
    root,u,_ = shapes[a]
    v,w = shapes[b][1],shapes[c][1]
    path = u+l+v+r+w
    history = [(len(u+l+v+r),c),(len(u+l),b),(0,a)]
    return dict(reflects=False,reason='bare reverse cube',witness=[root,path,history,[2,1,2],[1,2,1]])


def guarded_word_problem(relators):
    """All comparisons at width zero crossings read the ordinary group presentation."""
    def token(word):
        return [['p' if abs(g)==1 else 'q',0,1 if g>0 else -1] for g in word]
    if any(abs(g) not in (1,2) for w in relators for g in w):
        raise ValueError('expected a signed word in two generators')
    def face(n,l,r):
        return ['v','',[(0,'s')]*n,l,r]
    atoms = [face(3,[2,1,2],[1,2,1]),face(2,token((1,))+[1],token((2,))+[1])]
    for w in relators:
        atoms.extend([face(1,token(w),[]),face(1,[],token(w))])
    return dict(edges={},rules={'s':['v','','']},unary={'p':['s','s'],'q':['s','s']},
                attachments=atoms,query=face(2,token((1,)),token((2,))))


def checks():
    from semistrict_surface_framed_pair import decide
    from semistrict_surface_invertible_updates import solve as surface
    p = ['p',0,1]
    def face(n,a,b):
        return ['v','',[(0,'s')]*n,a,b]
    cube = face(3,[2,1,2],[1,2,1])
    base = dict(edges={},rules={'s':['v','','']},unary={'p':['s','s']})
    cases = total = 0
    for local, rev, rule in product((-1,0,1),(-1,0,1),(-2,-1,0,1,2)):
        def toks(k):
            return [['p',0,1 if k>=0 else -1]]*abs(k)
        local_moves = [k for k in (local,rev) if k]
        atoms = [face(1,[],toks(k)) for k in local_moves]+[cube,face(2,[1],toks(rule)+[1])]
        out = solve(dict(base,attachments=atoms))
        pair_rules = [[1,[0,[[0]]],[0,[[k]]]] for k in local_moves]
        pair_rules.append([2,[1,[[0],[0]]],[1,[[rule],[0]]]])
        oracle = decide(dict(rank=1,rules=pair_rules))
        assert out['reflects']==(oracle['failure'] is None)
        if not out['reflects']:
            assert surface(dict(base,attachments=atoms,query=out['witness']))['surface']
        cases += out['reflects']
        total += 1
    # An admissible forward label increment on a reverse cube cannot return
    # the undecorated cube unless that increment can also be undone locally.
    decorated = face(3,[2,1,2],[p,1,2,1])
    for anchors,reason in [([], 'crossing guard'),([face(1,[],[p])], 'bare reverse cube'),
                            ([face(1,[],[p]),face(1,[p],[])], None)]:
        result = solve(dict(base,attachments=[decorated,*anchors]))
        assert result.get('reason')==reason
    # Two distinct literal labels with a tree edge need only one colour cube.
    data = dict(edges={},rules={'a':['v','',''],'b':['v','','']},unary={'j':['a','b']},
                attachments=[['v','',[(0,'a'),(0,'b'),(0,'a')],[2,1,2],[1,2,1]]])
    assert solve(data)['reflects']
    # Finite nonabelian models check the one fixed old boundary on both sides
    # of a family where word problems in the local group govern reflection.
    from itertools import permutations
    universe = list(permutations(range(3)))
    unit = tuple(range(3))
    def mul(a,b):
        return tuple(a[i] for i in b)
    def value(word,a,b):
        ans=unit
        for name,_,sign in word:
            g = a if name=='p' else b
            ans = mul(ans,g if sign>0 else tuple(g.index(i) for i in unit))
        return ans
    def inverse(a):
        return tuple(a.index(i) for i in unit)
    def closure(letters):
        seen, queue = {unit}, [unit]
        for g in queue:
            for d in letters:
                k = mul(g,d)
                if k not in seen:
                    seen.add(k)
                    queue.append(k)
        return seen
    def one_step_orbit(pair, goal, deltas):
        seen, queue = {pair}, [pair]
        for x,y in queue:
            for d in deltas:
                for k in ((mul(d,x),y),(x,mul(d,y))):
                    if k not in seen:
                        seen.add(k)
                        queue.append(k)
        return goal in seen
    examples = separated = 0
    for rels in ([],[(1,-2)],[(1,1),(2,2,2)],[(1,2,-1,-2)],[(1,),(2,)]):
        data = guarded_word_problem(rels)
        for a,b in product(universe,repeat=2):
            image = closure((a,b))
            def conjugates(d):
                return {mul(mul(t,d),inverse(t)) for t in image}
            deltas = set()
            for atom in data['attachments'][2:]:
                delta = mul(value(atom[4],a,b),inverse(value(atom[3],a,b)))
                deltas.update(conjugates(delta))
            left,right = [(value(w,a,b),unit) for w in data['query'][3:]]
            local = one_step_orbit(left,right,deltas)
            assert local == (mul(b,inverse(a)) in closure(deltas))
            # Evaluate the guarded declaration after adjoining its signed
            # suffix; its directed defect can then act in either occurrence.
            guard = data['attachments'][1]
            u,v = (value([token for token in w if token!=1],a,b) for w in guard[3:])
            assert one_step_orbit(left,right,deltas|conjugates(mul(v,inverse(u))))
            examples += 1
            separated += not local
    assert separated
    print(f'{total} global tests agree with independent two-strand Presburger inclusion '
          f'({cases} reflecting), including verified surface witnesses for every guard failure. '
          f'One-way and reversible decorated cubes, tree colours and {examples} '
          f'finite quotient tests of the fixed old boundary ({separated} raw exclusions) checked.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--presentation',type=Path)
    group.add_argument('--encode-relators',type=Path)
    args = parser.parse_args()
    if args.presentation:
        print(json.dumps(solve(json.loads(args.presentation.read_text()))))
    elif args.encode_relators:
        print(json.dumps(guarded_word_problem(json.loads(args.encode_relators.read_text()))))
    else:
        checks()
