"""Two-slot ab/ba reflection for rules preserving both extreme marked prefixes.

--presentation FILE checks trimmed obligations, or raw and surface if a query
is present. --machine FILE compiles blank-input halting to all-boundary
reflection on the two orders. --limit caps explored states per query.
"""
from argparse import ArgumentParser
from collections import deque
from itertools import combinations_with_replacement, product
import json
from pathlib import Path

from semistrict_surface_frozen_words import Tape
from semistrict_surface_prism_counters import P, X, instructions_for, prefixes, state


def parse(h,w):
    if h not in ('ab','ba'):
        raise ValueError('expected one a and one b')
    list(prefixes(h,w,{P:'aa'}))
    n=0
    word=[]
    for x,_ in w:
        if x==X:
            n+=1
        else:
            word.append(n)
    return n,tuple(word)


def spelling(h,n,word):
    if sorted(word)!=list(word) or any(j<0 or j>n for j in word):
        raise ValueError('not a positive face')
    out=[]
    j=0
    for k in word:
        out.extend([(X,0)]*(k-j))
        out.append((P,(k+int(h=='ba'))%2))
        j=k
    return tuple(out+[(X,0)]*(n-j))


class Hull:
    def __init__(self,rules):
        self.rules=[]
        self.trimmed=[]
        for h,l,r in rules:
            n,a=parse(h,l)
            m,b=parse(h,r)
            if (n!=m or not a or not b or (a[0],a[-1])!=(b[0],b[-1])
                    or any((j+int(h=='ba'))%2==0 for j in a+b)):
                raise ValueError('expected right marks and preserved first and last prefixes')
            self.rules.append((h,n,a,b))
            base=a[0]
            self.trimmed.append(('ba',a[-1]-base,tuple(j-base for j in a),tuple(j-base for j in b)))

    def moves(self,h,n,w,mode):
        # signed is unrestricted prefix rewriting. positive-surface implements
        # its proven restriction to positive old endpoints by trimming.
        signed=mode=='signed'
        for i,j in enumerate(w):
            if (j+int(h=='ba'))%2==0:
                for b in (j-1,j+1):
                    if signed or (w[i-1] if i else 0)<=b<=(w[i+1] if i+1<len(w) else n):
                        yield w[:i]+(b,)+w[i+1:]
        for chart,m,a,b in (self.trimmed if mode=='positive-surface' else self.rules):
            for i in range(len(w)-len(a)+1):
                d=w[i]-a[0]
                end=i+len(a)
                if (h!=chart)!=bool(d%2):
                    continue
                if not signed and (d<(w[i-1] if i else 0) or d+m>(w[end] if end<len(w) else n)):
                    continue
                if all(w[i+j]==x+d for j,x in enumerate(a)):
                    yield w[:i]+tuple(x+d for x in b)+w[end:]

    def reach(self,h,n,a,b,mode,limit):
        todo=deque([a])
        seen={a}
        count=0
        while todo:
            w=todo.popleft()
            if w==b:
                return True
            if count==limit:
                return None
            count+=1
            for v in self.moves(h,n,w,mode):
                if v not in seen:
                    seen.add(v)
                    todo.append(v)
        return False

    def all(self,limit):
        obligations=[]
        # A truncated run is unknown. Other finite tests can still refute the
        # conjunction even if an earlier search has reached its limit.
        for h,n,a,b in dict.fromkeys(self.trimmed):
            ans=self.reach(h,n,a,b,'raw',limit)
            obligations.append(ans)
            if ans is False:
                return dict(reflects=False,witness=[h,spelling(h,n,a),spelling(h,n,b)])
        return dict(reflects=None if None in obligations else True,checks=len(obligations))


def compile_machine(machine):
    counts=machine.get('input',[0,0])
    ins=instructions_for(dict(machine,input=counts))
    tape=Tape([*ins,'done'])
    rules=[]
    def append(l,r,pad=False):
        low,hi=(0,tape.length) if pad else (l[0],l[-1])
        h='ab' if low%2==0 else 'ba'
        rules.append((h,spelling(h,hi-low,[j-low for j in l]),spelling(h,hi-low,[j-low for j in r])))
    def rule(q,r,k,kind):
        mark=(5,) if k==0 else (tape.right,)
        cap=(1,) if k==0 else (tape.cap,)
        def side(ctrl,copies):
            group=mark*copies
            if kind=='zero':
                group=cap+group if k==0 else group+cap
            return group+tape.codes[ctrl] if k==0 else tape.codes[ctrl]+group
        append(side(q,1+int(kind=='dec')),side(r,1+int(kind=='inc')))
    for q,(kind,k,*dest) in ins.items():
        if kind=='inc':
            rule(q,dest[0],k,'inc')
        else:
            rule(q,dest[0],k,'zero')
            rule(q,dest[1],k,'dec')
    source=tape.config(state(machine['start']),1+counts[0],1+counts[1])
    target=tape.config('done',1,1)
    append(source,target,pad=True)
    return dict(rules=rules)


def compile_strings(data):
    """Equal-length substring rules; all tests except the padded query are tight."""
    src,dst=map(tuple,(data['source'],data['target']))
    rows=[(tuple(l),tuple(r)) for l,r in data['rules']]
    alphabet=sorted({x for l,r in rows+[(src,dst)] for x in l+r})
    ids={x:i for i,x in enumerate(alphabet)}
    pitch=20+4*len(ids)
    def word(w):
        return tuple(j*pitch+t for j,x in enumerate(w)
                     for t in (1,3,9+4*ids[x],15+4*len(ids)))
    rules=[]
    for i,(l,r) in enumerate(rows+[(src,dst)]):
        if not l or len(l)!=len(r):
            raise ValueError('expected nonempty equal-length word pairs')
        a,b=word(l),word(r)
        padded=i==len(rows)
        low,high=(0,a[-1]+1) if padded else (a[0],a[-1])
        h='ab' if padded else 'ba'
        rules.append((h,spelling(h,high-low,[j-low for j in a]),spelling(h,high-low,[j-low for j in b])))
    return dict(rules=rules)


def closure(start,moves):
    todo=[start]
    seen={start}
    for w in todo:
        for v in moves(w):
            if v not in seen:
                seen.add(v)
                todo.append(v)
    return seen


def checks():
    # All rules in these dictionaries conserve word length; signed extreme
    # heights are bounded by the initial range plus one. Exhaustion is exact.
    choices=[]
    for pad in (0,1):
        for source,target in [((0,0,2),(0,2,2)),((0,2,4),(0,0,4))]:
            h='ab' if pad else 'ba'
            n=target[-1]+2*pad
            choices.append((h,spelling(h,n,[x+pad for x in source]),spelling(h,n,[x+pad for x in target])))
    starts=pairs=0
    for mask in range(1<<len(choices)):
        model=Hull([v for i,v in enumerate(choices) if mask>>i&1])
        for h in ('ab','ba'):
            for n in (2,4):
                for m in range(4):
                    old=set(combinations_with_replacement(range(n+1),m))
                    for start in old:
                        signed=closure(start,lambda w:model.moves(h,n,w,'signed'))
                        positive=closure(start,lambda w:model.moves(h,n,w,'positive-surface'))
                        assert signed&old==positive
                        starts+=1
                        pairs+=len(old)
    yes=dict(start='s',halt='h',program={'s':['inc',1,'t'],'t':['test',1,'h','t']})
    no=dict(start='s',halt='h',program={'s':['inc',0,'d'],'d':['test',0,'h','s']})
    assert Hull(compile_machine(yes)['rules']).all(1000)['reflects'] is True
    assert Hull(compile_machine(no)['rules']).all(1000)['reflects'] is False
    strings=0
    for system in [[],[('01','10')],[('0','1'),('11','00')]]:
        def substr(w):
            for l,r in system:
                for i in range(len(w)-len(l)+1):
                    if w.startswith(l,i):
                        yield w[:i]+r+w[i+len(l):]
        words=[''.join(w) for w in product('01',repeat=3)]
        for u in words:
            seen=closure(u,substr)
            for v in words:
                d=compile_strings(dict(rules=system,source=u,target=v))
                assert Hull(d['rules']).all(1000)['reflects']==(v in seen)
                strings+=1
    return dict(finite_dictionaries=16,initial_faces=starts,old_face_pairs=pairs,
                reflecting_halt=True,nonreflecting_cycle=True,balanced_string_queries=strings)


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    src=p.add_mutually_exclusive_group()
    src.add_argument('--presentation',type=Path)
    src.add_argument('--machine',type=Path)
    src.add_argument('--strings',type=Path)
    p.add_argument('--limit',type=int,default=10000)
    args=p.parse_args()
    if args.machine:
        result=compile_machine(json.loads(args.machine.read_text()))
    elif args.strings:
        result=compile_strings(json.loads(args.strings.read_text()))
    elif args.presentation:
        data=json.loads(args.presentation.read_text())
        model=Hull(data['rules'])
        if 'query' not in data:
            result=model.all(args.limit)
        else:
            h,l,r=data['query']
            n,a=parse(h,l)
            m,b=parse(h,r)
            result={k:n==m and model.reach(h,n,a,b,mode,args.limit)
                    for k,mode in [('raw','raw'),('surface','positive-surface')]}
    else:
        result=checks()
    print(json.dumps(result))
