"""Decide exhausted frozen-word searches at two scalar occurrences.

--pair FILE compiles two 2-counter programs starting with the same two inputs.
JSON keys are x, y (machines as in semistrict_surface_prism_counters.py) and
optional input (default [0,0]). The x branch uses a surface-only entry, the y
branch is raw-executable. --faces FILE searches both judgments of an instance.
Only reporting a reached target or exhausting a graph decides that instance.
"""
from argparse import ArgumentParser
from collections import deque
from itertools import product
import json
from pathlib import Path

from semistrict_surface_prism_counters import Literal, P, X, instructions_for, state


def frozen(movie):
    height=0
    marks=[]
    for x,i in movie:
        if x==X and i==0:
            height+=1
        elif x==P and i==1:
            marks.append(height)
        else:
            raise ValueError('expected positive two-slot crossings and right-position marks')
    if not marks or any((j-marks[0])%2 for j in marks):
        raise ValueError('expected nonempty markings of a single input occurrence')
    return height,tuple(marks)


def face(length,marks):
    if sorted(marks)!=list(marks) or any(not 0<=j<=length for j in marks):
        raise ValueError('expected a positive spelling')
    out=[]
    j=0
    for k in marks:
        out.extend([(X,0)]*(k-j))
        out.append((P,1))
        j=k
    return tuple(out+[(X,0)]*(length-j))


def signed_segment(start,marks,end):
    out=[]
    for k in (*marks,end):
        sign=1 if start<=k else -1
        out.extend([sign]*abs(k-start))
        out.append(P)
        start=k
    return out[:-1]


def replay(steps):
    j=0
    marks=[]
    for op in steps:
        if op==P:
            marks.append(j)
        else:
            j+=op
    return j,tuple(marks)


class Frozen:
    def __init__(self,data):
        if data['history']!='aa' or data['labels']!={P:'aa'}:
            raise ValueError('expected two scalar occurrences and one unary loop')
        self.length,self.start=frozen(data['source'])
        n,self.end=frozen(data['target'])
        self.parallel=(n,self.end[0]%2)==(self.length,self.start[0]%2)
        self.rules=[]
        for name,h,l,r in data['attachments']:
            if h!='aa':
                raise ValueError('expected full two-slot rules')
            n,a=frozen(l)
            m,b=frozen(r)
            if n!=m or (a[0]-b[0])%2:
                raise ValueError('rule must preserve crossing word and named occurrence')
            self.rules.append((name,n,a,b))

    def moves(self,w,signed,verify=False):
        for name,n,a,b in self.rules:
            for i in range(len(w)-len(a)+1):
                shift=w[i]-a[0]
                end=i+len(a)
                if any(w[i+k]!=shift+j for k,j in enumerate(a)):
                    continue
                if not signed:
                    lo=w[i-1] if i else 0
                    hi=w[end] if end<len(w) else self.length
                    if shift<lo or shift+n>hi:
                        continue
                other=w[:i]+tuple(shift+j for j in b)+w[end:]
                if verify:
                    pre=signed_segment(0,w[:i],shift)
                    post=signed_segment(shift+n,w[end:],self.length)
                    for v,marks in ((w,a),(other,b)):
                        local=signed_segment(shift,[shift+j for j in marks],shift+n)
                        assert -1 not in local and replay(pre+local+post)==(self.length,v)
                    if not signed:
                        assert -1 not in pre+post
                yield name,other

    def search(self,signed,limit):
        if not self.parallel:
            return dict(inhabited=False,explored=0)
        seen={self.start}
        todo=deque([self.start])
        explored=0
        while todo:
            w=todo.popleft()
            if w==self.end:
                return dict(inhabited=True,explored=explored)
            if explored==limit:
                return dict(inhabited=None,explored=explored)
            explored+=1
            for _,v in self.moves(w,signed):
                if v not in seen:
                    seen.add(v)
                    todo.append(v)
        return dict(inhabited=False,explored=explored)


class Tape:
    def __init__(self,states):
        self.codes={q:(9,11,17+4*i,23+4*len(states)) for i,q in enumerate(sorted(states))}
        self.right=27+4*len(states)
        self.cap=self.right+4
        self.length=self.cap+1
        self.rules=[]

    def config(self,q,a,b):
        return (1,)+(5,)*a+self.codes[q]+(self.right,)*b+(self.cap,)

    def step(self,name,q,r,op=None,k=0,padded=False):
        l=self.codes[q]
        t=self.codes[r]
        token=(5,) if k==0 else (self.right,)
        border=(1,) if k==0 else (self.cap,)
        def include(word,part):
            return part+word if k==0 else word+part
        if op=='zero':
            l,t=include(l,border),include(t,border)
        if op=='dec':
            l=include(l,token)
        if op=='inc':
            t=include(t,token)
        lo,hi=(0,self.length) if padded else (min(l[0],t[0]),max(l[-1],t[-1]))
        self.rules.append((name,'aa',face(hi-lo,[j-lo for j in l]),face(hi-lo,[j-lo for j in t])))

    def program(self,prefix,ins):
        for q,(op,k,*dest) in ins.items():
            if op=='inc':
                self.step(prefix+'inc',prefix+q,prefix+dest[0],'inc',k)
            else:
                self.step(prefix+'zero',prefix+q,prefix+dest[0],'zero',k)
                self.step(prefix+'dec',prefix+q,prefix+dest[1],'dec',k)
        self.step(prefix+'finish',prefix+'done','final')

    def query(self,q,a,b):
        return dict(history='aa',labels={P:'aa'},attachments=self.rules,
                    source=face(self.length,self.config(q,a,b)),target=face(self.length,self.config('final',0,0)))


def compile_pair(data):
    input_counts=data.get('input',[0,0])
    states={'initial','final'}
    programs=[]
    for key in ('x','y'):
        m=dict(data[key],input=input_counts)
        ins=instructions_for(m)
        prefix=key+'/'
        states.update(prefix+q for q in (*ins,'done'))
        programs.append((prefix,ins,prefix+state(m['start'])))
    tape=Tape(states)
    for prefix,ins,first in programs:
        tape.step(prefix+'enter','initial',first,padded=prefix=='x/')
        tape.program(prefix,ins)
    return tape,tape.query('initial',*input_counts)


def checks():
    yes=dict(start='s',halt='h',program={'s':['test',1,'h','s']})
    no=dict(start='s',halt='h',program={'s':['inc',0,'d'],'d':['test',0,'h','s']})
    pairs=states=raw_edges=signed_edges=0
    for x,y in product((False,True),repeat=2):
        tape,data=compile_pair(dict(x=yes if x else no,y=yes if y else no,input=[1,2]))
        solver=Frozen(data)
        raw=solver.search(False,1000)['inhabited']
        signed=solver.search(True,1000)['inhabited']
        assert (raw,signed)==(y,x or y)
        pairs+=1
        literal=Literal(data)
        for q in tape.codes:
            for a,b in product(range(2),repeat=2):
                cfg=tape.config(q,a,b)
                w=face(tape.length,cfg)
                actual={(name,frozen(v)[1]) for name,v in literal.steps(w)}
                predicted=set(solver.moves(cfg,False))
                assert actual==predicted
                general=set(solver.moves(cfg,True,verify=True))
                assert general-predicted==({('x/enter',tape.config('x/q/s',a,b))} if q=='initial' else set())
                assert predicted<=general
                states+=1
                raw_edges+=len(actual)
                signed_edges+=len(general)
    return dict(halting_pairs=pairs,configurations=states,raw_edges=raw_edges,surface_edges=signed_edges)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    opt=parser.add_mutually_exclusive_group()
    opt.add_argument('--pair',type=Path)
    opt.add_argument('--faces',type=Path)
    parser.add_argument('--limit',type=int,default=10000)
    args=parser.parse_args()
    if args.pair:
        _,result=compile_pair(json.loads(args.pair.read_text()))
    elif args.faces:
        solver=Frozen(json.loads(args.faces.read_text()))
        result={name:solver.search(signed,args.limit) for name,signed in [('raw',False),('surface',True)]}
    else:
        result=checks()
    print(json.dumps(result))
