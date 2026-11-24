"""Compile a two-counter program to a two-slot one-missing-return surface query.

--machine FILE uses the prism_counters program format. --faces FILE searches
the resulting conserved-energy instance; a live search cut off is undetermined.
"""
from argparse import ArgumentParser
from collections import Counter, deque
from itertools import product
import json
from pathlib import Path

from semistrict_surface_positive_movies import windows
from semistrict_surface_prism_counters import P, X, instructions_for, prefixes, state


def marks(i,shift=0):
    offsets=(0,1,3,6,10+5*i)
    return tuple(40*i+shift+k for k in offsets)


def registers(a,b):
    return marks(0)+marks(1,a)+marks(2)+marks(3,b)


def spelling(word,labels,length):
    out=[(x,0) for x in labels]
    prefix=0
    for k in word:
        j=2*k+1
        if not prefix<=j<=length:
            raise ValueError('nonpositive attachment writing')
        out.extend([(X,0)]*(j-prefix))
        out.append((P,1))
        prefix=j
    return tuple(out+[(X,0)]*(length-prefix))


def compile_machine(machine):
    ins=instructions_for(machine)
    names=(P,'c0','c1','in0','in1','entry','load0','load1',*ins,'done')
    labels={x:'aa' for x in names}
    length=2*registers(0,0)[-1]+2
    rules=[]
    def add(kind,h,l,r):
        if list(prefixes(h,l,labels))[-1]!=list(prefixes(h,r,labels))[-1]:
            raise ValueError('nonparallel rule')
        rules.append((kind,h,l,r))
    for x,y in product(names,repeat=2):
        if x!=y:
            add('commute','a',((x,0),(y,0)),((y,0),(x,0)))
    omitted=0
    for c,d in product('ab',repeat=2):
        for kind,l,r in windows(2,labels):
            label=next(x for x,_ in l if x!=X)
            side=int(kind=='left')
            if (c,d)[side]!='a':
                continue
            if (c,d,side,label)==('a','b',0,P):
                omitted+=1
            else:
                add('prism',c+d,r,l)
    assert omitted==1
    def rewrite(name,a,b,take,give,pad=None):
        support=a+b
        base=min(support,default=0)
        last=2*(max(support,default=base)-base)+1
        size=last if pad is None else pad
        def side(word,tokens):
            return spelling(tuple(k-base for k in word),tokens,size)
        add(name,'ab',side(a,take),side(b,give))
    def shift(q,r,k,delta,extra=()):
        c='c'+str(k)
        take=(q,)+extra+((c,) if delta==-1 else ())
        give=(r,)+((c,) if delta==1 else ())
        which=2*k+1
        rewrite('shift',marks(which),marks(which,delta),take,give)
    rewrite('entry',(),(),('entry',),('load0',),length+2)
    for k in range(2):
        q='load'+str(k)
        shift(q,q,k,1,('in'+str(k),))
        rewrite('advance',(),(),(q,),(('load1' if k==0 else state(machine['start'])),))
    for q,(op,k,*dest) in ins.items():
        if op=='inc':
            shift(q,dest[0],k,1)
        else:
            pair=marks(2*k)+marks(2*k+1)
            rewrite('test',pair,pair,(q,),(dest[0],))
            shift(q,dest[1],k,-1)
    a,b=machine['input']
    return dict(history='ab',labels=labels,attachments=rules,
                source=spelling(registers(0,0),['entry']+['in0']*a+['in1']*b,length),
                target=spelling(registers(0,0),['done'],length))


def record(w,start=0):
    k=start
    word=[]
    mobile=Counter()
    for x,i in w:
        if x==X:
            k+=1
        elif x==P:
            word.append((k-1)//2)
        else:
            mobile[x]+=1
    return k-start,tuple(word),mobile


def raw_states(data):
    """Overapproximate raw control reachability, forgetting all label demands."""
    length=sum(x==X for x,_ in data['source'])
    fixed={P,'c0','c1','in0','in1'}
    states={'entry'}
    edges=[]
    for _,h,l,r in data['attachments']:
        if h not in ('a','ab','ba') or sum(x==X for x,_ in l)>length:
            continue
        a=[x for x,_ in l if x in data['labels'] and x not in fixed]
        b=[x for x,_ in r if x in data['labels'] and x not in fixed]
        if len(a)==len(b)==1:
            edges.append((a[0],b[0]))
        elif Counter(a)!=Counter(b):
            raise ValueError('finite control invariant violated')
    while True:
        more={v for u,v in edges if u in states}-states
        if not more:
            return states
        states.update(more)


class Winding:
    """Search equal-energy signed readings with one partially mobile label."""
    def __init__(self,data):
        if data['history']!='ab' or any(v!='aa' for v in data['labels'].values()):
            raise ValueError('expected one label-bearing a strand at ab')
        for w in (data['source'],data['target']):
            list(prefixes('ab',w,data['labels']))
        length,self.start_word,self.start_mobile=record(data['source'])
        n,self.end_word,self.end_mobile=record(data['target'])
        self.length=length
        self.mobile=tuple(x for x in data['labels'] if x!=P)
        def energy(w,t):
            return sum(w)-5*(t['c0']+t['c1'])
        if length!=n or energy(self.start_word,self.start_mobile)!=energy(self.end_word,self.end_mobile):
            raise ValueError('expected equal structural words and endpoint energy')
        self.rules=[]
        commutes=set()
        returns=set()
        for _,h,l,r in data['attachments']:
            if h not in ('a','ab','ba'):
                continue
            list(prefixes(h,l,data['labels']))
            list(prefixes(h,r,data['labels']))
            l,r=tuple(map(tuple,l)),tuple(map(tuple,r))
            if h=='a':
                if len(l)==2 and l==r[::-1]:
                    commutes.add(tuple(x for x,_ in l))
                    continue
                raise ValueError('width-one rules must be unary commutations')
            for kind,left,right in windows(2,data['labels']):
                x=next(t for t,_ in left if t!=X)
                side=int(kind=='left')
                if h[side]=='a' and l==right and r==left:
                    returns.add((h,x))
            initial=int(h=='ba')
            n,a,t=record(l,initial)
            m,b,v=record(r,initial)
            if n!=m or len(a)!=len(b) or energy(a,t)!=energy(b,v):
                raise ValueError('attachment outside the conserved-energy sector')
            if (a,t)!=(b,v):
                self.rules.append((a,b,t,v,initial,l,r))
        if any((x,y) not in commutes for x,y in product(data['labels'],repeat=2) if x!=y):
            raise ValueError('missing unary commutation')
        required={(h,x) for h,x in product(('ab','ba'),data['labels']) if (h,x)!=('ab',P)}
        if returns!=required:
            raise ValueError('expected exactly the ab return for p to be omitted')
        self.start=self.config(self.start_word,self.start_mobile)
        self.end=self.config(self.end_word,self.end_mobile)

    def config(self,w,t):
        return w,tuple(t[x] for x in self.mobile)

    def steps(self,cfg,verify=False):
        w,counts=cfg
        tokens=Counter(dict(zip(self.mobile,counts)))
        for a,b,t,v,initial,l,r in self.rules:
            if not t<=tokens:
                continue
            for i in range(len(w)-len(a)+1 if a else 1):
                shift=w[i]-a[0] if a else 0
                if all(w[i+j]==s+shift for j,s in enumerate(a)):
                    new=w[:i]+tuple(s+shift for s in b)+w[i+len(a):]
                    if verify:
                        for word,body,demand in ((w,l,t),(new,r,v)):
                            _,placed,used=record(body,initial+2*shift)
                            assert used==demand and word[i:i+len(placed)]==placed
                    yield self.config(new,tokens-t+v)

    def search(self,limit):
        todo=deque([self.start])
        seen={self.start}
        expanded=0
        while todo:
            cfg=todo.popleft()
            if cfg==self.end:
                return dict(surface=True,explored=expanded)
            if expanded==limit:
                return dict(surface=None,explored=expanded)
            expanded+=1
            for nxt in self.steps(cfg):
                if nxt not in seen:
                    seen.add(nxt)
                    todo.append(nxt)
        return dict(surface=False,explored=expanded)


def checks():
    machine=dict(start='s',halt='h',input=[1,2],program={
        's':['test',0,'r','t'],'t':['inc',1,'s'],
        'r':['test',1,'h','u'],'u':['inc',0,'r']})
    data=compile_machine(machine)
    model=Winding(data)
    result=model.search(1000)
    assert result['surface']
    count=0
    for q,(op,k,*dest) in instructions_for(machine).items():
        for a,b in product((0,1,5,40,83),repeat=2):
            t=Counter({q:1,'c0':a,'c1':b})
            n=(a,b)[k]
            v=[a,b]
            v[k]+=1 if op=='inc' else -int(n>0)
            r=dest[0] if op=='inc' or not n else dest[1]
            expected=model.config(registers(*v),Counter({r:1,'c0':v[0],'c1':v[1]}))
            assert set(model.steps(model.config(registers(a,b),t),verify=True))=={expected}
            count+=1
    loop=dict(start='s',halt='h',input=[0,0],program={'s':['inc',0,'t'],'t':['test',0,'h','s']})
    assert Winding(compile_machine(loop)).search(100)['surface'] is False
    assert raw_states(data)=={'entry'}
    # Every actual instruction preserves the aggregate block height minus
    # the five companion counts; a native spill raises it by exactly one.
    return dict(instruction_configurations=count,p_tokens=len(model.start_word),
                positive_search=result,cyclic_negative=True,crossings=model.length,
                raw_accessible_control=sorted(raw_states(data)))


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    mode=parser.add_mutually_exclusive_group()
    mode.add_argument('--machine',type=Path)
    mode.add_argument('--faces',type=Path)
    parser.add_argument('--limit',type=int,default=10000)
    args=parser.parse_args()
    if args.machine:
        result=compile_machine(json.loads(args.machine.read_text()))
    elif args.faces:
        result=Winding(json.loads(args.faces.read_text())).search(args.limit)
    else:
        result=checks()
    print(json.dumps(result))
