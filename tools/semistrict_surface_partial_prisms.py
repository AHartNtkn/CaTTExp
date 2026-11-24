"""Compile a two-slot scalar raw query to a counter system with exact guards.

Use --presentation FILE, optionally --petri to require ordinary net output.
--machine FILE compiles a four-slot simulation missing a single prism return.
The JSON structures follow semistrict_surface_prism_counters.py.
"""
from argparse import ArgumentParser
from collections import Counter, deque
from itertools import product
import json
from pathlib import Path

from semistrict_surface_prism_counters import (
    BASE, P, X, Literal, chambers, instructions_for, prefixes, state)
from semistrict_surface_positive_movies import windows


def counter_system(data):
    h=data['history']
    labels=data['labels']
    if len(h)!=2 or X in labels or any(len(v)!=2 or v[0]!=v[1] for v in labels.values()):
        raise ValueError('expected two scalar occurrences and endomorphism labels')
    def read(base,w):
        list(prefixes(base,w,labels))
        return chambers(w)
    length,start=read(h,data['source'])
    n,end=read(h,data['target'])
    if length!=n:
        return dict(source=[1],target=[0],transitions=[],places=['different crossing counts'])
    charts=[h if j%2==0 else h[::-1] for j in range(length+1)]
    moves=[]
    returns=set()
    commute=set()
    for _,base,l,r in data['attachments']:
        if len(base)>2 or not base:
            continue
        m,need=read(base,l)
        if read(base,r)[0]!=m:
            raise ValueError('rule changes its structural braid')
        _,give=chambers(r)
        if len(base)==1 and len(l)==2 and list(l)==list(reversed(r)):
            commute.add(tuple(x for x,_ in l))
        for j in range(length-m+1):
            for pos in range(3-len(base)):
                if charts[j][pos:pos+len(base)]!=base:
                    continue
                def place(row):
                    return Counter({(j+k,(pos+e)^(j%2),x):v for (k,e,x),v in row.items()})
                a,b=place(need),place(give)
                if a==b:
                    continue
                moves.append((j,m,a,b))
                if m==1 and a.total()==b.total()==1:
                    (s,e,x),=a
                    (t,f,y),=b
                    if (e,x)==(f,y) and s!=t and e^(s%2)==1:
                        returns.add((j,e,x))
    for c in h:
        names=[x for x,v in labels.items() if v[0]==c]
        if any((x,y) not in commute for x,y in product(names,repeat=2) if x!=y):
            raise ValueError('supply both same-strand unary commutations')
    ids={}
    places=[]
    native=[]
    for e,c in enumerate(h):
        for x,ends in labels.items():
            if ends[0]!=c:
                continue
            left=0
            for j in range(length+1):
                ids[j,e,x]=len(places)
                if j==length or (j,e,x) not in returns:
                    places.append((left,j,e,x))
                    left=j+1
            for j in range(length):
                u,v=ids[j,e,x],ids[j+1,e,x]
                if u!=v:
                    native.append((u,v) if e^(j%2)==0 else (v,u))
    def vector(bag):
        out=[0]*len(places)
        for key,n in bag.items():
            out[ids[key]]+=n
        return tuple(out)
    def unit(i):
        return tuple(int(j==i) for j in range(len(places)))
    edges={(unit(i),unit(j),()) for i,j in native}
    for j,m,a,b in moves:
        take,give=vector(a),vector(b)
        if take!=give:
            exact=tuple(i for i,(s,t,_,_) in enumerate(places) if j<s and t<j+m)
            edges.add((take,give,exact))
    return dict(places=places,source=vector(start),target=vector(end),transitions=sorted(edges))


def petri(system):
    if any(exact for _,_,exact in system['transitions']):
        raise ValueError('a rule encloses a reversible component and requires an exact guard')
    return dict(source=system['source'],target=system['target'],
                transitions=[(a,b) for a,b,_ in system['transitions']])


def one_missing(machine):
    ins=instructions_for(machine)
    ins['init']=('test',0,state(machine['halt']),state(machine['start']))
    names=(*ins,'done')
    labels={P:'aa',**{q:'bb' for q in names}}
    rules=[]
    def add(kind,h,l,r):
        if list(prefixes(h,l,labels))[-1]!=list(prefixes(h,r,labels))[-1]:
            raise ValueError('nonparallel rule')
        rules.append((kind,h,l,r))
    for x,y in product(names,repeat=2):
        if x!=y:
            add('commute','b',((x,0),(y,0)),((y,0),(x,0)))
    missing=0
    for c,d in product('ab',repeat=2):
        for kind,l,r in windows(2,labels):
            label=next(x for x,_ in l if x!=X)
            side=int(kind=='left')
            if (c,d)[side]!=labels[label][0]:
                continue
            if (c,d,side,label)==('a','b',0,P):
                missing+=1
            else:
                add('prism',c+d,r,l)
    assert missing==1
    def instruction(q,k,r,action):
        zero=action=='zero'
        h=('b' if k else '')+('ab' if zero else 'ba')
        control=int(zero and not k)
        cross=((X,k),)*(3 if zero else 1)
        token=((P,k),)
        l=((q,control),)+cross+(token if action=='dec' else ())
        t=((r,control),)+cross+(token if action=='inc' else ())
        add(action,h,l,t)
    for q,(kind,k,*dest) in ins.items():
        if kind=='inc':
            instruction(q,k,dest[0],'inc')
        else:
            instruction(q,k,dest[0],'zero')
            instruction(q,k,dest[1],'dec')
    a,b=machine['input']
    def face(q,a,b):
        return (((q,1),)+((X,0),)*2+((P,0),)*a+((X,0),)+
                ((X,2),)*2+((P,2),)*b+((X,2),))
    return dict(history=BASE,labels=labels,attachments=rules,
                source=face('init',a+1,b),target=face('done',0,0))


def check_two():
    labels={P:'aa'}
    situations=0
    bounded_cases=0
    for mask in range(4):
        returns=[]
        for i,h in enumerate(('ab','ba')):
            for kind,l,r in windows(2,labels):
                side=int(kind=='left')
                if mask>>i&1 and h[side]=='a':
                    returns.append(('return',h,r,l))
        for span in (1,2,3):
            cross=((X,0),)
            # The initial a switches position at each crossing.
            rules=returns+[('read','ab',cross+((P,1),)+cross*(span-1),cross*span)]
            data=dict(history='ab',labels=labels,attachments=rules,source=cross*4,target=cross*4)
            sys=counter_system(data)
            if mask.bit_count()>=1 and span<=2:
                petri(sys)
                bounded_cases+=1
            if mask==2 and span==3:
                assert any(exact for _,_,exact in sys['transitions'])
            literal=Literal(data)
            groups={}
            def project(w):
                _,bag=chambers(w)
                return tuple(sum(bag[j,e,x] for j in range(s,t+1)) for s,t,e,x in sys['places'])
            for counts in product(range(3),repeat=5):
                if sum(counts)>2:
                    continue
                word=tuple(ev for j,n in enumerate(counts)
                           for ev in (((P,j%2),)*n+(cross if j<4 else ())))
                old=project(word)
                got=groups.setdefault(old,set())
                got.update(project(v) for _,v in literal.steps(word))
            for old,got in groups.items():
                got.discard(old)
                predicted={tuple(v-a+b for v,a,b in zip(old,take,give))
                           for take,give,exact in sys['transitions']
                           if all(a<=v for a,v in zip(take,old)) and all(old[i]==take[i] for i in exact)}
                predicted.discard(old)
                assert got==predicted,(mask,span,old,got,predicted)
                situations+=1
    return situations,bounded_cases


def profile(movie):
    perm=list(range(4))
    crossings=[0,0]
    live=[0,0]
    waste=[0,0]
    ctrl=None
    for x,i in movie:
        if x==X:
            assert i in (0,2)
            crossings[i//2]+=1
            perm[i],perm[i+1]=perm[i+1],perm[i]
        elif x==P:
            k=perm[i]//2
            assert perm[i]%2==0 and crossings[k]>0
            (waste if crossings[k]==3 else live)[k]+=1
        else:
            assert ctrl is None and perm[i]==1
            ctrl=x
    assert ctrl is not None and crossings==[3,3]
    return ctrl,tuple(live),tuple(waste)


def witness(q,live,waste):
    out=[(q,1)]
    for k,(n,w) in enumerate(zip(live,waste)):
        i=2*k
        out+= [(X,i)]*2+[(P,i)]*n+[(X,i)]+[(P,i+1)]*w
    return tuple(out)


def check_simulation():
    machine=dict(start='s',halt='h',input=[1,0],program={
        's':['test',0,'t','u'],'t':['inc',1,'s'],'u':['test',1,'h','v'],'v':['inc',0,'u']})
    data=one_missing(machine)
    ins=instructions_for(machine)
    ins['init']=('test',0,state('h'),state('s'))
    literal=Literal(data)
    checked=readings=leaks=0
    for q in ins:
        for live,waste in [((0,0),(0,0)),((1,0),(0,0)),((0,1),(0,0)),((0,0),(1,0)),((0,0),(0,1))]:
            cfg=q,live,waste
            op,k,*dest=ins[q]
            n=live[k]
            after=list(live)
            after[k]+=1 if op=='inc' else -int(n>0)
            expected=(dest[0] if op=='inc' or not n else dest[1],tuple(after),waste)
            root=witness(*cfg)
            todo=deque([root])
            seen={root}
            progress=set()
            while todo:
                w=todo.popleft()
                for kind,v in literal.steps(w):
                    out=profile(v)
                    if kind in ('zero','inc','dec'):
                        progress.add(out)
                    elif out==cfg:
                        if v not in seen:
                            seen.add(v)
                            todo.append(v)
                    else:
                        ctrl,new_live,new_waste=out
                        assert ctrl==q and sum(new_waste)==sum(waste)+1
                        assert all(w<=v for w,v in zip(waste,new_waste))
                        assert all(a+b==c+d for a,b,c,d in zip(live,waste,new_live,new_waste))
                        leaks+=1
            assert progress=={expected},(cfg,progress,expected)
            checked+=1
            readings+=len(seen)
    assert profile(data['source'])==('init',(2,0),(0,0))
    assert profile(data['target'])==('done',(0,0),(0,0))
    return checked,readings,leaks


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    src=parser.add_mutually_exclusive_group()
    src.add_argument('--presentation',type=Path)
    src.add_argument('--machine',type=Path)
    parser.add_argument('--petri',action='store_true')
    args=parser.parse_args()
    if args.presentation:
        result=counter_system(json.loads(args.presentation.read_text()))
        if args.petri:
            result=petri(result)
    elif args.machine:
        result=one_missing(json.loads(args.machine.read_text()))
    else:
        classes,bounds=check_two()
        cases,readings,leaks=check_simulation()
        result=dict(two_slot_classes=classes,ordinary_net_cases=bounds,simulated_configurations=cases,
                    literal_readings=readings,irreversible_leak_edges=leaks)
    print(json.dumps(result))
