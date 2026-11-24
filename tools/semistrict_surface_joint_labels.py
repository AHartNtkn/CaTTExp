"""Decide all-boundary reflection with arbitrary braid-preserving mixed 4-rules.

Input is the invertible_updates presentation format with commuting unary cycles.
Crossing-free rules may require any finite temporal and spatial context.
"""
from argparse import ArgumentParser
from collections import defaultdict, deque
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_braid_reflection import certify, end_vertex
from semistrict_surface_guarded_labels import separate
from semistrict_surface_history_group import exchange, placements
from semistrict_surface_invertible_updates import Colours, Faces
from semistrict_surface_scalar_sites import coefficients



def positive_normal(n,word):
    """Left-greedy positive factors, each encoded by its output permutation."""
    identity = list(range(n))
    factors = []
    for g in word:
        if not 1<=g<n:
            raise ValueError('crossing outside the positive braid')
        atom = identity.copy()
        atom[g-1],atom[g] = atom[g],atom[g-1]
        factors.append(atom)
    j = 0
    while j+1<len(factors):
        left,right = factors[j:j+2]
        where = [0]*n
        for pos,name in enumerate(right):
            where[name] = pos
        for i in range(n-1):
            if left[i]<left[i+1] and where[i]>where[i+1]:
                left[i],left[i+1] = left[i+1],left[i]
                a,b = where[i],where[i+1]
                right[a],right[b] = right[b],right[a]
                j = max(0,j-1)
                break
        else:
            j += 1
    return tuple(tuple(p) for p in factors if p!=identity)

class Rule(Faces):
    def __init__(self,data,entry,cols):
        super().__init__(data,entry,cols)
        l,r = [separate(self.original,m,cols) for m in self.movies]
        if positive_normal(len(self.history),l[0])!=positive_normal(len(self.history),r[0]):
            raise ValueError('rule changes the structural braid')
        self.crosses = l[0],r[0]
        self.delta = tuple(tuple(b-a for a,b in zip(x,y)) for x,y in zip(l[2],r[2]))
        self.final = self.path
        for p,c in self.history:
            a,b = cols.marks[c]
            self.final = self.final[:p]+b+self.final[p+len(a):]


class GapWords:
    def __init__(self,edges,words):
        self.out = defaultdict(list)
        for e,(a,b) in edges.items():
            self.out[a].append((e,b))
        self.substrings = {''}
        for w in words:
            self.substrings.update(w[i:j] for i in range(len(w)) for j in range(i+1,len(w)+1))

    @lru_cache(None)
    def step(self, state, e):
        prefix, full, suffix = state
        full = full and prefix+e in self.substrings
        if full:
            prefix += e
        suffix += e
        while suffix not in self.substrings:
            suffix = suffix[1:]
        return prefix,full,suffix

    @lru_cache(None)
    def paths(self,start,end):
        initial = ('',True,'')
        todo = deque([(start,initial,'')])
        seen = {(start,initial)}
        found = []
        while todo:
            v,state,w = todo.popleft()
            if v==end and w:
                found.append(w)
            for e,y in self.out[v]:
                k = self.step(state,e)
                if (y,k) not in seen:
                    seen.add((y,k))
                    todo.append((y,k,w+e))
        return found


class Catalogue:
    def __init__(self,data):
        self.data, self.cols = data, Colours(data)
        self.edges = data['edges']
        if any(len(e)!=1 for e in self.edges):
            raise ValueError('edge identifiers must be single characters')
        for c,axes in self.cols.cycles.items():
            if any(frozenset(pair) not in self.cols.commutations for pair in combinations(axes,2)):
                raise ValueError(f'noncommuting label axes at {c}')
        self.shapes = {c:data['rules'][c] for c in self.cols.cycles}
        for v,a,b in self.shapes.values():
            if end_vertex(self.edges,v,a)!=end_vertex(self.edges,v,b):
                raise ValueError('nonparallel base rule')
        self.rules = [Rule(data,entry,self.cols) for entry in data['attachments']]
        self.zeros = [r for r in self.rules if not r.crosses[0] and any(any(row) for row in r.delta)]
        self.gaps = GapWords(self.edges,(r.path for r in self.zeros))
        self.stats = dict(internal=0,boundary=0,guard=0)
        self.empty = (0,)*len(self.cols.axis)

    @lru_cache(None)
    def rows(self,v,path,h):
        return {tuple(x for row in ((self.empty,)*k+a.delta+(self.empty,)*(len(h)-len(a.delta)-k)) for x in row)
                for k,a in placements(h,v,path,self.zeros,self.edges,self.cols.marks)}

    def accepts(self,v,path,h,delta):
        return coefficients(tuple(self.rows(v,path,h)), tuple(x for row in delta for x in row)) is not None

    def overlaps(self,r,c,before):
        """Trim stationary whiskers at the common slice, then enumerate gap classes."""
        v,a,b = self.shapes[c]
        middle, side = (r.path,b) if before else (r.final,a)
        def merged(offset):
            lo,hi = min(0,offset),max(len(middle),offset+len(side))
            s = [None]*(hi-lo)
            s[-lo:len(middle)-lo] = middle
            for i,x in enumerate(side,offset-lo):
                if s[i] is not None and s[i]!=x:
                    return
                s[i]=x
            path = ''.join(s)
            return (v if offset<0 else r.root),path,-lo,offset-lo
        def slices():
            for d in range(-len(side),len(middle)+1):
                m = merged(d)
                if m is not None:
                    yield m
            for g in self.gaps.paths(end_vertex(self.edges,r.root,middle),v):
                yield r.root,middle+g+side,0,len(middle)+len(g)
            for g in self.gaps.paths(end_vertex(self.edges,v,side),r.root):
                yield v,side+g+middle,len(side)+len(g),0
        for root,mid,p,q in slices():
            try:
                if end_vertex(self.edges,root,mid[:p])!=r.root or end_vertex(self.edges,root,mid[:q])!=v:
                    continue
                end_vertex(self.edges,root,mid)
            except ValueError:
                continue
            h = tuple((i+p,x) for i,x in r.history)
            if before:
                yield root,mid[:q]+a+mid[q+len(b):],((q,c),)+h,(self.empty,)+r.delta,1
            else:
                yield root,mid[:p]+r.path+mid[p+len(middle):],h+((q,c),),r.delta+(self.empty,),len(h)

    def witness(self,v,path,h,delta):
        # Lift each integer axis to a loop at the literal input generator.
        links = defaultdict(list)
        for name,(a,b) in self.cols.arrows.items():
            if name not in self.cols.axis:
                links[a].append((name,1,b))
                links[b].append((name,-1,a))
        def tree(a,b,e):
            queue, paths = [a], {a:[]}
            for x in queue:
                if x==b:
                    return paths[x]
                for name,sign,y in links[x]:
                    if y not in paths:
                        paths[y] = paths[x]+[[name,e,sign]]
                        queue.append(y)
            raise AssertionError('missing tree path')
        word = []
        for e,((_,c),row) in enumerate(zip(h,delta)):
            for name,index in self.cols.axis.items():
                k = row[index]
                if k:
                    a,b = self.cols.arrows[name]
                    if k<0:
                        a,b=b,a
                    cycle = tree(c,a,e)+[[name,e,1 if k>0 else -1]]+tree(b,c,e)
                    word.extend(cycle*abs(k))
        return [v,path,h,[],word]

    def transported(self,root,path,h,delta,i,kind):
        for g in (i,-i):
            k=exchange(h,g,self.cols.marks)
            if k is None:
                continue
            self.stats[kind]+=1
            ds = list(delta)
            ds[i-1:i+1]=ds[i-1:i+1][::-1]
            if not self.accepts(root,path,k,ds):
                return dict(reflects=False,reason='transport of crossing-free rule',edge=g,
                            origin=h,witness=self.witness(root,path,k,ds),checks=self.stats)

    def solve(self):
        for r in self.zeros:
            m=len(r.history)
            for i in range(1,m):
                bad = self.transported(r.root,r.path,r.history,r.delta,i,'internal')
                if bad:
                    return bad
            for c in self.shapes:
                for before in (True,False):
                    for args in self.overlaps(r,c,before):
                        bad=self.transported(*args,'boundary')
                        if bad:
                            return bad
        cubes = []
        for r in self.rules:
            if not r.crosses[0]:
                continue
            self.stats['guard']+=1
            if not self.accepts(r.root,r.path,r.history,r.delta):
                return dict(reflects=False,reason='crossing guard',
                            witness=self.witness(r.root,r.path,r.history,r.delta),checks=self.stats)
            if r.crosses==((2,1,2),(1,2,1)) and self.accepts(r.root,r.path,r.history,
                                                               [tuple(-x for x in row) for row in r.delta]):
                cubes.append([r.root,r.path,r.history,*r.crosses])
        missing=certify(dict(edges=self.edges,rules=self.shapes,attachments=cubes))
        if missing is None:
            return dict(reflects=True,checks=self.stats)
        (a,b,c),(l,r)=missing
        v,u,_=self.shapes[a]
        w,z=self.shapes[b][1],self.shapes[c][1]
        h=[(len(u+l+w+r),c),(len(u+l),b),(0,a)]
        return dict(reflects=False, reason='bare reverse cube',
                    witness=[v,u+l+w+r+z,h,[2,1,2],[1,2,1]],checks=self.stats)


def checks():
    from itertools import permutations, product
    from random import Random
    from semistrict_surface_guarded_labels import solve as local
    rng=Random(172)
    def face(word,delta):
        return ['v','',[(0,c) for c in word],[],[[c.upper(),i,1] for i,(c,y) in enumerate(zip(word,delta)) for _ in range(y)]]
    shapes = dict(edges={},rules={c:['v','',''] for c in 'st'},unary={c.upper():[c,c] for c in 'st'})
    cubes=[['v','',[(0,c) for c in w],[2,1,2],[1,2,1]] for w in product('st',repeat=3)]
    tests=good=compared=0
    for _ in range(48):
        dictionary=[]
        for n in (1,2):
            for w in product('st',repeat=n):
                for d in product((0,1),repeat=n):
                    if any(d) and rng.randrange(4)==0:
                        dictionary.append((w,d))
        base=dict(shapes,attachments=[face(w,d) for w,d in dictionary]+cubes)
        result=Catalogue(base).solve()
        expected=True
        for n in range(1,4):
            for h in product('st',repeat=n):
                raw,signed=set(),set()
                for w,d in dictionary:
                    for i in range(n-len(w)+1):
                        if h[i:i+len(w)]==w:
                            raw.add((0,)*i+d+(0,)*(n-i-len(w)))
                    for sites in permutations(range(n),len(w)):
                        if tuple(h[i] for i in sites)==w:
                            v=[0]*n
                            for j,x in zip(sites,d):
                                v[j]=x
                            signed.add(tuple(v))
                def reachable(rows):
                    seen,todo={(0,)*n},[(0,)*n]
                    for v in todo:
                        for d in rows:
                            z=tuple(x+y for x,y in zip(v,d))
                            if max(z)<=1 and z not in seen:
                                seen.add(z)
                                todo.append(z)
                    return seen
                expected &= reachable(raw)==reachable(signed)
                compared += 1
        assert expected==result['reflects']
        good+=expected
        tests+=1
    for m in range(2,8):
        joint=face('s'*m,(1,)*m)
        negative=Catalogue(dict(shapes,attachments=[joint,*cubes])).solve()
        assert not negative['reflects'] and len(negative['witness'][2])==m+1
    # A death takes away the edge required by a guarded zero-crossing scalar
    # update, although the scalar and death are executable in either order.
    spatial=dict(edges={'x':['v','v'],'y':['v','v']},
                 rules={'u':['v','','x'],'d':['v','x',''],'s':['v','','']},
                 unary={'p':['s','s'],'q':['u','u']})
    one=['v','x',[(1,'s')],[],[['p',0,1]]]
    only=Catalogue(dict(spatial,attachments=[one])).solve()
    assert only['reason']=='transport of crossing-free rule'
    Faces(spatial,only['witness'],Colours(spatial))
    two=['v','xy',[(1,'u'),(1,'d')],[],[['q',0,1]]]
    three=['v','yx',[(1,'s')],[],[['p',0,1],['p',0,1]]]
    model=Catalogue(dict(spatial,attachments=[one,two,three]))
    r=model.rules[1]
    def boundary(g,c,before,right):
        _,a,b=model.shapes[c]
        if right:
            path=r.path+g+a
            q=len(r.path if before else r.final)+len(g)
            extra=((q,c),)
            return path,(extra+r.history if before else r.history+extra)
        path=a+g+r.path
        d=len(b if before else a)+len(g)
        h=tuple((p+d,x) for p,x in r.history)
        return path,(((0,c),)+h if before else h+((0,c),))
    long_tests=0
    for tup in product('xy',repeat=7):
        g=''.join(tup)
        shorter=g[:2]+'x'+g[-2:]
        for c,before,right in product(model.shapes,(False,True),(False,True)):
            p,h=boundary(g,c,before,right)
            q,k=boundary(shorter,c,before,right)
            i=1 if before else len(r.history)
            for a in (0,i,-i):
                x,y=(exchange(h,a,model.cols.marks),exchange(k,a,model.cols.marks)) if a else (h,k)
                assert (x is None)==(y is None)
                if x is not None:
                    assert model.rows('v',p,x)==model.rows('v',q,y)
                    long_tests+=1
    one_base=dict(edges={},rules={'s':['v','','']},unary={'S':['s','s']})
    for atoms in ([face('s',(1,))],[],[face('s',(1,)),['v','',[(0,'s')]*3,[2,1,2],[1,2,1]]]):
        d=dict(one_base,attachments=atoms)
        assert Catalogue(d).solve()['reflects']==local(d)['reflects']
    print(f'{tests} two-colour dictionaries agree with direct bounded raw and signed '
          f'reachability at {compared} words ({good} reflecting). Sharp widths 3 through 8, '
          f'a spatial death obstruction and {long_tests} long-gap placement comparisons checked.')


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--presentation',type=Path)
    args=parser.parse_args()
    if args.presentation:
        print(json.dumps(Catalogue(json.loads(args.presentation.read_text())).solve()))
    else:
        checks()
