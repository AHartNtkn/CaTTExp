"""Compile signed two-slot queries with at most two persistent partial updates.

For the normalized finite presentation, labels maps unary names to a or b.
returns lists, by label, ordered charts ("ab", "ba") supplying the reverse
prism. All unary commutations are supplied. Rules are [chart,left,right] and
source/target are literal positive movies on ab. Output is a finite-control
Petri net, optionally with a single tested place.
"""
from argparse import ArgumentParser
from collections import Counter, deque
from itertools import product
import json
from pathlib import Path

from semistrict_surface_prism_counters import X, prefixes
from semistrict_surface_partial_prisms import counter_system
from semistrict_surface_positive_movies import windows


def read(word,h,labels,partial):
    pairs={x:c+c for x,c in labels.items()}
    list(prefixes(h,word,pairs))
    j=0
    marks=[]
    counts=Counter()
    for x,_ in word:
        if x==X:
            j+=1
        elif x in partial:
            marks.append((x,j))
        else:
            counts[x]+=1
    return j,marks,counts


class Checkpoints:
    def __init__(self,data):
        self.labels=data['labels']
        if X in self.labels or any(c not in ('a','b') for c in self.labels.values()):
            raise ValueError('expected unary labels at a or b')
        self.returns={x:set(data['returns'].get(x,[])) for x in self.labels}
        self.partial={x for x,r in self.returns.items() if not {'ab','ba'}<=r}
        self.mobile=tuple(x for x in self.labels if x not in self.partial)
        def parse(w,h):
            return read(w,h,self.labels,self.partial)
        self.length,self.start,self.s=parse(data['source'],'ab')
        n,self.end,self.t=parse(data['target'],'ab')
        self.fit=n==self.length and len(self.start)==len(self.end)
        self.rules=[]
        for h,l,r in data['rules']:
            if h not in ('ab','ba','a','b'):
                raise ValueError('expected a one- or two-slot rule')
            m,a,u=parse(l,h)
            z,b,v=parse(r,h)
            if m!=z or len(a)!=len(b):
                raise ValueError('rules must preserve crossing and partial-token counts')
            self.rules.append((h,a,b,u,v))

    @staticmethod
    def control(marks):
        return tuple((x,j%2) for x,j in marks)

    def raw(self,data):
        pairs={x:c+c for x,c in self.labels.items()}
        rules=[('rule',*r) for r in data['rules']]
        for x,y in product(pairs,repeat=2):
            if x!=y and pairs[x]==pairs[y]:
                rules.append(('commute',self.labels[x],[(x,0),(y,0)],[(y,0),(x,0)]))
        for h in ('ab','ba'):
            for kind,l,r in windows(2,pairs):
                x=next(v for v,_ in l if v!=X)
                if h[int(kind=='left')]==self.labels[x] and h in self.returns[x]:
                    rules.append(('return',h,r,l))
        if not self.fit:
            return dict(source=[1],target=[0],transitions=[])
        net=counter_system(dict(history='ab',labels=pairs,source=data['source'],target=data['target'],
                                attachments=rules))
        small=[i for i,p in enumerate(net['places']) if p[3] in self.partial]
        free=[i for i in range(len(net['places'])) if i not in small]
        def part(v,indices):
            return tuple(v[i] for i in indices)
        initial=part(net['source'],small)
        final=part(net['target'],small)
        states,ids,edges=[initial],{initial:0},set()
        for i,m in enumerate(states):
            for a,b,exact in net['transitions']:
                assert all(j in small for j in exact)
                d=tuple(v-a[j] for j,v in zip(small,m))
                if min(d,default=0)<0 or any(d[small.index(j)] for j in exact):
                    continue
                new=tuple(v+b[j] for j,v in zip(small,d))
                if new not in ids:
                    ids[new]=len(states)
                    states.append(new)
                edges.add((i,ids[new],part(a,free),part(b,free)))
        if final not in ids:
            return dict(source=[1],target=[0],transitions=[])
        def tag(i):
            return tuple(int(j==i) for j in range(len(states)))
        return dict(source=tag(0)+part(net['source'],free),target=tag(ids[final])+part(net['target'],free),
                    transitions=[(tag(i)+a,tag(j)+b) for i,j,a,b in sorted(edges)])

    def actions(self,ctrl):
        """Yield target control, coordinate increments, optional gap test and mobile arcs."""
        k=len(ctrl)
        def shift(i,old,new,newnames):
            change=[0]*k
            out=list(ctrl)
            for offset,(a,b,name) in enumerate(zip(old,new,newnames)):
                change[i+offset]=b-a
                out[i+offset]=name,(ctrl[i+offset][1]+b-a)%2
            dx=change[0] if k else 0
            dg=change[1]-dx if k==2 else 0
            return tuple(out),dx,dg
        for i,(x,p) in enumerate(ctrl):
            left=(self.labels[x]=='a')==(p==0)
            for delta in (-1,1):
                chart=('ab','ba')[min(p,p+delta)%2]
                if left or chart in self.returns[x]:
                    yield (*shift(i,[0],[delta],[x]),None,Counter(),Counter())
        if k==2 and ctrl[0][1]==ctrl[1][1] and ctrl[0][0]!=ctrl[1][0]:
            yield ctrl[::-1],0,0,0,Counter(),Counter()
        for h,a,b,u,v in self.rules:
            for i in range(k-len(a)+1 if a else 1):
                if any(ctrl[i+t][0]!=x for t,(x,j) in enumerate(a)):
                    continue
                if a:
                    translation=(ctrl[i][1]-a[0][1])%2
                    if len(h)==2 and translation!=int(h=='ba'):
                        continue
                    if any((j+translation)%2!=ctrl[i+t][1] for t,(_,j) in enumerate(a)):
                        continue
                old=[j for _,j in a]
                new=[j for _,j in b]
                guard=old[1]-old[0] if len(a)==2 else None
                yield (*shift(i,old,new,[x for x,_ in b]),guard,u,v)

    def compile(self):
        k=len(self.start)
        if k>2:
            raise ValueError('the one-tested-place reduction allows at most two partial tokens')
        if not self.fit:
            return dict(places=[],edges=[],source=['s',[]],target=['t',[]],tested=None)
        places=['label:'+x for x in self.mobile]
        if k:
            places+=['first+','first-']
        if k==2:
            places+=['gap']
        ids={}
        edges=[]
        def ident(key):
            if key not in ids:
                ids[key]=len(ids)
            return ids[key]
        def vec(t):
            return tuple(t[x] for x in places)
        def edge(a,b,t=(),v=(),test=False):
            edges.append((ident(a),ident(b),vec(Counter(t)),vec(Counter(v)),test))
        signs=(1,-1) if k==2 else (1,)
        initial=self.control(self.start)
        seen={initial}
        stack=[initial]
        seq=0
        while stack:
            ctrl=stack.pop()
            if k==2:
                for s in signs:
                    edge((ctrl,s),(ctrl,-s),test=True)
            for dst,dx,dg,guard,t,v in self.actions(ctrl):
                if dst not in seen:
                    seen.add(dst)
                    stack.append(dst)
                seq+=1
                t=Counter({'label:'+x:n for x,n in t.items()})
                add=Counter({'label:'+x:n for x,n in v.items()})
                if dx:
                    add['first+' if dx>0 else 'first-']+=abs(dx)
                if guard is not None:
                    # Consume a known magnitude, check exact exhaustion, then
                    # restore the known resulting signed displacement.
                    s=1 if guard>=0 else -1
                    after=guard+dg
                    take=Counter(t)
                    take['gap']+=abs(guard)
                    add['gap']+=abs(after)
                    edge((ctrl,s),('guard',seq),take)
                    edge(('guard',seq),(dst,1 if after>=0 else -1),v=add,test=True)
                elif dg:
                    for s in signs:
                        edge((ctrl,s),('move',seq,0,s),t)
                    unit=1 if dg>0 else -1
                    for j in range(abs(dg)):
                        for s in signs:
                            here=('move',seq,j,s)
                            there=('move',seq,j+1,s)
                            edge(here,('move',seq,j,-s),test=True)
                            if s==unit:
                                edge(here,there,v=['gap'])
                            else:
                                edge(here,there,t=['gap'])
                    for s in signs:
                        edge(('move',seq,abs(dg),s),(dst,s),v=add)
                else:
                    for s in signs:
                        edge((ctrl,s),(dst,s),t,add)
        goal=self.control(self.end)
        for s in signs:
            edge((goal,s),('end',s))
            if k:
                edge(('end',s),('end',s),['first+','first-'])
        def marking(marks,t,final):
            values=Counter({'label:'+x:n for x,n in t.items()})
            g=0
            if k:
                x=marks[0][1]
                values['first+' if x>=0 else 'first-']=abs(x)
            if k==2:
                g=marks[1][1]-x
                values['gap']=abs(g)
            s=1 if g>=0 else -1
            key=('end',s) if final else (self.control(marks),s)
            return ident(key),vec(values)
        return dict(places=places,source=marking(self.start,self.s,False),target=marking(self.end,self.t,True),
                    edges=edges,tested='gap' if k==2 else None)


def search(net,limit):
    source=(net['source'][0],tuple(net['source'][1]))
    target=(net['target'][0],tuple(net['target'][1]))
    todo=deque([source])
    seen={source}
    by={}
    for a,b,t,v,z in net['edges']:
        by.setdefault(a,[]).append((b,t,v,z))
    i=net['places'].index('gap') if net['tested'] else None
    expanded=0
    while todo:
        node=todo.popleft()
        if node==target:
            return True
        if expanded==limit:
            return None
        expanded+=1
        state,m=node
        for b,t,v,z in by.get(state,()):
            if (not z or m[i]==0) and all(n>=a for n,a in zip(m,t)):
                nxt=b,tuple(n-a+c for n,a,c in zip(m,t,v))
                if nxt not in seen:
                    seen.add(nxt)
                    todo.append(nxt)
    return False


def translate_net(net):
    """One general zero-tested Petri place, or two independently tested counter instructions."""
    s,t=net['source'],net['target']
    d=len(s)
    tested=net['tested']
    if tested not in ([0],[0,1]) or max(tested)>=d or len(t)!=d:
        raise ValueError('expected initial tested place(s) 0, or 0 and 1')
    if any(type(i)!=int or i<0 for row in (s,t) for i in row):
        raise ValueError('invalid marking')
    base=2+max(s[0],t[0])
    center='anchor'
    regs=['r'+str(i) for i in tested]
    mob=['m'+str(i) for i in range(d)]
    labels={x:'a' for x in (center,*regs,*mob)}
    def points(v):
        result=[(base,center)]
        for i,r in zip(tested,regs):
            sign=-1 if i==0 else 1
            result.append((base+sign*(2+v[i]),r))
        return sorted(result)
    def spelling(p,w,n):
        out=[(x,0) for x,z in zip(mob,w) for _ in range(z)]
        j=0
        for k,x in p:
            h=2*k+1
            if h<j or h>n:
                raise ValueError('ill-ordered counter pattern')
            out.extend([(X,0)]*(h-j))
            out.append((x,1))
            j=h
        return out+[(X,0)]*(n-j)
    length=2*max(k for v in (s,t) for k,_ in points(v))+2
    rules=[]
    for take,give,guard in net['transitions']:
        if len(take)!=d or len(give)!=d or any(type(v)!=int or v<0 for v in (*take,*give)):
            raise ValueError('invalid arc')
        if guard is not None and guard not in tested:
            raise ValueError('unknown zero test')
        if guard is not None and take[guard]:
            continue
        active={i for i in tested if take[i]!=give[i]}
        if guard is not None:
            active.add(guard)
        if len(active)>1:
            raise ValueError('two-counter instruction must act on one tested register')
        a,b=[],[]
        if active:
            i,=active
            sign=-1 if i==0 else 1
            x=base+2*sign
            a=[(x,regs[i])]
            b=[(x+sign*(give[i]-take[i]),regs[i])]
            if guard is not None:
                a=sorted(a+[(base,center)])
                b=sorted(b+[(base,center)])
        low=min((k for k,_ in a+b),default=0)
        high=max((k for k,_ in a+b),default=0)
        n=2*(high-low)+1
        rules.append(('ab',spelling([(k-low,x) for k,x in a],take,n),
                      spelling([(k-low,x) for k,x in b],give,n)))
    return dict(labels=labels,returns={x:(['ba'] if x not in mob else ['ab','ba']) for x in labels},
                rules=rules,source=spelling(points(s),s,length),target=spelling(points(t),t,length))


def checks():
    # Audit finite-control schemas against literal translated pattern matching
    # on both signs, including crossed named strands and unequal input charts.
    data=dict(labels={'p':'a','q':'b','z':'a'},returns={'p':['ba'],'z':['ab','ba']},
              source=[('p',0),('q',1)],target=[('q',1),('p',0)],rules=[
                  ('ab',[('p',0),(X,0),('q',0)],[(X,0),('q',0),('p',1)]),
                  ('ba',[(X,0),('p',0)],[('p',1),(X,0)]),
                  ('a',[('z',0)],[('z',0),('z',0)])])
    model=Checkpoints(data)
    checks=0
    for x,y in product(range(-3,4),repeat=2):
        for u,v in [('p','q'),('q','p')]:
            actual=set()
            marks=((u,x),(v,y))
            for i,(label,j) in enumerate(marks):
                left=(label=='p')==(j%2==0)
                for delta in (-1,1):
                    chart=('ab','ba')[min(j,j+delta)%2]
                    if left or chart in model.returns[label]:
                        a=list(marks)
                        a[i]=label,j+delta
                        actual.add((tuple(a),0))
            if x==y:
                actual.add((marks[::-1],0))
            actual.add((marks,1))
            if (u,v)==('p','q') and y==x+1 and x%2==0:
                actual.add(((('q',y),('p',y)),0))
            j=x if u=='p' else y
            if j%2==0:
                a=list(marks)
                a[0 if u=='p' else 1]=('p',j-1)
                actual.add((tuple(a),0))
            predicted=set()
            for dst,dx,dg,g,take,give in model.actions(model.control(marks)):
                if g is None or y-x==g:
                    js=(x+dx,y+dx+dg)
                    out=tuple((label,j) for (label,parity),j in zip(dst,js))
                    assert all(j%2==p for j,(_,p) in zip(js,dst))
                    predicted.add((out,give['z']-take['z']))
            assert predicted==actual,(marks,actual,predicted)
            checks+=1
    assert search(model.compile(),1000)
    raw=model.raw(data)
    assert search(dict(places=list(range(len(raw['source']))),source=(0,raw['source']),
                       target=(0,raw['target']),tested=None,
                       edges=[(0,0,t,v,False) for t,v in raw['transitions']]),100)
    # The emitted signed-gap test consumes exactly its specified magnitude.
    unit=dict(labels={'p':'a','q':'a','go':'a','ok':'a'},
              returns={'go':['ab','ba'],'ok':['ab','ba']},rules=[
                  ('ab',[('go',0),('p',0),(X,0),(X,0),('q',0)],
                   [('ok',0),('p',0),(X,0),(X,0),('q',0)])])
    good=Checkpoints(dict(unit,source=unit['rules'][0][1],target=unit['rules'][0][2])).compile()
    assert search(good,1000)
    # Native moves cannot leave a right-position checkpoint with no returns.
    locked=[(X,0),('p',1),('q',1)]
    bad=Checkpoints(dict(unit,source=[('go',0)]+locked,target=[('ok',0)]+locked)).compile()
    assert search(bad,1000) is False
    encoded=translate_net(dict(tested=[0],source=[0,0],target=[0,1],
                               transitions=[([0,0],[0,1],0)]))
    assert search(Checkpoints(encoded).compile(),10000)
    # Compare both tested registers with literal translated groups. Endpoint
    # order stays r0,anchor,r1 even when a register has negative signed height.
    arcs=[([0,0],[1,0],None),([0,1],[0,0],None),([0,0],[0,2],1),([0,0],[2,0],0)]
    two=translate_net(dict(tested=[0,1],source=[0,0],target=[0,0],transitions=arcs))
    marked={'anchor','r0','r1'}
    def blocks(side):
        _,w,t=read(side,'ab',two['labels'],marked)
        return [(x,(j-1)//2) for x,j in w],t
    def positions(a,b):
        return [('r0',-a),('anchor',2),('r1',4+b)]
    cases=0
    for a,b in product(range(5),repeat=2):
        tokens=Counter(m0=a,m1=b)
        w=positions(a,b)
        outcomes=set()
        for _,l,r in two['rules']:
            old,need=blocks(l)
            new,give=blocks(r)
            for i in range(4-len(old)):
                shift=w[i][1]-old[0][1]
                if need<=tokens and w[i:i+len(old)]==[(x,j+shift) for x,j in old]:
                    out=w[:i]+[(x,j+shift) for x,j in new]+w[i+len(old):]
                    v=tokens-need+give
                    assert out==positions(v['m0'],v['m1'])
                    outcomes.add((v['m0'],v['m1']))
        expected={tuple(n-u+v for n,u,v in zip((a,b),take,give)) for take,give,g in arcs
                  if all(n>=u for n,u in zip((a,b),take)) and (g is None or (a,b)[g]==0)}
        assert outcomes==expected
        cases+=1
    return dict(signed_configurations=checks,one_test_positive=True,
                exhausted_frozen_negative=True,reverse_net_reduction=True,three_token_configurations=cases)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    opt=parser.add_mutually_exclusive_group()
    opt.add_argument('--presentation',type=Path)
    opt.add_argument('--encode-net',type=Path)
    parser.add_argument('--limit',type=int)
    parser.add_argument('--raw',action='store_true',help='export the ordinary raw reachability net')
    parser.add_argument('--decide',action='store_true',help='run the complete decision with islpy')
    args=parser.parse_args()
    if args.encode_net:
        result=translate_net(json.loads(args.encode_net.read_text()))
    elif args.presentation:
        data=json.loads(args.presentation.read_text())
        model=Checkpoints(data)
        result=model.raw(data) if args.raw else model.compile()
        if args.decide and args.limit is not None:
            raise ValueError('choose either a complete or a bounded search')
        if args.decide:
            if args.raw:
                from semistrict_surface_positive_labels import reachable
                result=dict(raw=reachable(result))
            else:
                from semistrict_surface_one_test_reachability import decide
                result=dict(surface=decide(result))
        if args.raw and args.limit is not None:
            raise ValueError('--limit is for the signed finite-control search')
        if args.limit is not None:
            result=dict(surface=search(result,args.limit))
    else:
        result=checks()
    print(json.dumps(result))
