"""Decide individual mixed 4-types with commuting labels and braid-preserving rules.

--presentation FILE uses the invertible_updates format. --encode-rewriting FILE
compiles a length-preserving substring system on strings into a three-event query.
"""
from argparse import ArgumentParser
from functools import lru_cache
from itertools import product
import json
from pathlib import Path

from semistrict_surface_component_order import weighted_walk
from semistrict_surface_guarded_labels import separate
from semistrict_surface_history_group import exchange, placements
from semistrict_surface_invertible_updates import Faces
from semistrict_surface_joint_labels import Catalogue, positive_normal
from semistrict_surface_scalar_sites import coefficients


class Fibre:
    def __init__(self,data):
        self.catalogue = Catalogue(data)
        self.cols = self.catalogue.cols
        self.q = Faces(data,data['query'],self.cols)
        self.n = len(self.q.history)
        self.rank = len(self.cols.axis)
        self.start = tuple((p,e) for e,(p,_) in enumerate(self.q.history))
        self.ports = {e:self.cols.marks[c] for e,(_,c) in enumerate(self.q.history)}
        left,right = (separate(self.q.original,m,self.cols) for m in self.q.movies)
        self.a,self.b = left[0],right[0]
        self.delta = tuple(v-u for xs,ys in zip(left[2],right[2]) for u,v in zip(xs,ys))
        self.zero = (0,)*len(self.delta)

    @lru_cache(None)
    def options(self,h):
        shape = tuple((p,self.q.history[e][1]) for p,e in h)
        placed = []
        for k,r in placements(shape,self.q.root,self.q.path,self.catalogue.rules,self.catalogue.edges,self.cols.marks):
            v = list(self.zero)
            for (_,e),row in zip(h[k:],r.delta):
                v[e*self.rank:(e+1)*self.rank] = row
            a,b = (tuple(k+g for g in w) for w in r.crosses)
            placed.append((a,b,tuple(v)))
        return placed

    def signed(self):
        if not any(self.delta):
            return True
        seen, todo, rows = {self.start},[self.start],set()
        for h in todo:
            rows.update(v for _,_,v in self.options(h) if any(v))
            for j in range(1,self.n):
                for g in (j,-j):
                    k = exchange(h,g,self.ports)
                    if k is not None and k not in seen:
                        seen.add(k)
                        todo.append(k)
        return coefficients(sorted(rows),self.delta) is not None

    def moves(self,w):
        h = self.start
        for j in range(len(w)+1):
            for a,b,v in self.options(h):
                if w[j:j+len(a)]==a:
                    yield w[:j]+b+w[j+len(a):],v
            if j==len(w):
                break
            g = w[j]
            if j+1<len(w) and abs(w[j+1]-g)>=2:
                yield w[:j]+(w[j+1],g)+w[j+2:],self.zero
            if w[j:j+3]==(g,g+1,g):
                yield w[:j]+(g+1,g,g+1)+w[j+3:],self.zero
            h=exchange(h,g,self.ports)
            assert h is not None

    def raw(self):
        words, ids, edges = [self.a],{self.a:0},set()
        for i,w in enumerate(words):
            for k,v in self.moves(w):
                if k not in ids:
                    ids[k]=len(words)
                    words.append(k)
                edges.add((i,ids[k],v,()))
        if self.b not in ids:
            return False,len(words)
        if not any(any(v) for _,_,v,_ in edges):
            return not any(self.delta),len(words)
        return weighted_walk(len(words),edges,ids[self.b],self.delta),len(words)

    def solve(self):
        if positive_normal(self.n,self.a)!=positive_normal(self.n,self.b):
            return dict(surface=False,raw=False,reflection_failure=False)
        if not self.signed():
            return dict(surface=False,raw=False,reflection_failure=False)
        answer,states = self.raw()
        return dict(surface=True,raw=answer,reflection_failure=not answer,positive_words=states)


def encode(data):
    rules = [tuple(pair) for pair in data['rules']]
    alphabet = sorted(set(''.join([data['source'],data['target'],*(s for pair in rules for s in pair)])))
    bits = max(1,(len(alphabet)-1).bit_length())
    letters = ('21221','12212')
    codes = {}
    for i,c in enumerate(alphabet):
        payload = ''.join('22'+letters[int(b)]+'22' for b in format(i,f'0{bits}b'))
        codes[c] = '22111122'+payload
    def spell(w):
        return [int(g) for c in w for g in codes[c]]
    def entry(a,b):
        if len(a)!=len(b):
            raise ValueError('rewriting instance must preserve length')
        return ['v','',[(0,'s')]*3,spell(a),spell(b)]
    return dict(edges={},rules={'s':['v','','']},attachments=[entry(a,b) for a,b in rules if a!=b],
                query=entry(data['source'],data['target']))


def checks():
    from random import Random
    from semistrict_surface_framed_pair import face, moves, point, relation
    rng=Random(174)
    old_pairs = list(product('ab',repeat=2))
    pairs=[''.join(s) for s in old_pairs]
    tests=good=0
    for _ in range(95):
        rules=[(rng.choice(pairs),rng.choice(pairs)) for _ in range(4)]
        a,b=(''.join(rng.choices('ab',k=4)) for _ in range(2))
        seen,todo={a},[a]
        for s in todo:
            for l,r in rules:
                for j in range(3):
                    if s[j:j+2]==l:
                        t=s[:j]+r+s[j+2:]
                        if t not in seen:
                            seen.add(t)
                            todo.append(t)
        data=encode(dict(rules=rules,source=a,target=b))
        out=Fibre(data).solve()
        assert out['surface'] and out['raw']==(b in seen) and out['positive_words']==len(seen)
        tests+=1
        good+=out['raw']
    def annotated(n,l,r):
        def old(side):
            count,rows = side
            return [['p',i,1 if v[0]>=0 else -1] for i,v in enumerate(rows) for _ in range(abs(v[0]))]+[1]*count
        return ['v','',[(0,'s')]*n,old(l),old(r)]
    outcomes=set()
    for _ in range(90):
        rules=[]
        for _ in range(3):
            n=rng.choice((1,2))
            k=rng.randrange(3) if n==2 else 0
            rules.append([n,[k,[[rng.randrange(-1,2)] for _ in range(n)]],[k,[[rng.randrange(-1,2)] for _ in range(n)]]])
        k=rng.randrange(3)
        a,b=([k,[[rng.randrange(-2,3)] for _ in range(2)]] for _ in range(2))
        data=dict(edges={},rules={'s':['v','','']},unary={'p':['s','s']},
                  attachments=[annotated(*r) for r in rules],query=annotated(2,a,b))
        out=Fibre(data).solve()
        x,y=face(a,2,1)[1],face(b,2,1)[1]
        target=point([k,k,*[v-u for u,v in zip(x,y)]])
        answers=tuple(not relation(1,moves(1,rules),signed).is_disjoint(target) for signed in (False,True))
        assert (out['raw'],out['surface'])==answers
        outcomes.add(answers)
    assert len(outcomes)==3
    from itertools import combinations
    from semistrict_surface_label_certificates import cover
    subsets=[comb for k in range(1,4) for comb in combinations(range(3),k)]
    for mask in range(128):
        family=[s for i,s in enumerate(subsets) if mask>>i&1]
        data=cover(dict(universe=list(range(3)),subsets=family))
        data['attachments']=data['attachments'][:-2]
        data['query']=['v','',[(0,'s')],[],[[f'd{i}',0,1] for i in range(3)]]
        expected=any(sorted(e for s in subset for e in s)==[0,1,2]
                     for k in range(4) for subset in combinations(family,k))
        out=Fibre(data).solve()
        assert out['raw']==out['surface']==expected
    # The reverse cube deposits a label at input zero each time around the
    # positive word cycle. Signed contexts can deposit it on another input.
    h=[(0,'s')]*3
    rev=['v','',h,[2,1,2],[['p',0,1],1,2,1]]
    for slot,k in ((0,1),(0,7),(1,1),(0,0)):
        d=dict(edges={},rules={'s':['v','','']},unary={'p':['s','s']},attachments=[rev],
               query=['v','',h,[2,1,2],[['p',slot,1]]*k+[1,2,1]])
        out=Fibre(d).solve()
        assert out['surface'] and out['raw']==(slot==0 and k>0)
    print(f'{tests} protected substring systems preserve the whole reachable graph ({good} reachable queries); '
          '90 mixed comparisons agree with the independent two-strand Presburger decisions, '
          'including surface-only, raw and uninhabited queries. 128 width-one exact covers '
          'and four marked three-strand word cycles checked.')


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group()
    group.add_argument('--presentation',type=Path)
    group.add_argument('--encode-rewriting',type=Path)
    args=parser.parse_args()
    if args.presentation:
        print(json.dumps(Fibre(json.loads(args.presentation.read_text())).solve()))
    elif args.encode_rewriting:
        print(json.dumps(encode(json.loads(args.encode_rewriting.read_text()))))
    else:
        checks()
