"""Realize a list of private strand checkpoints in a simple positive interval.

--checkpoints FILE specifies initial and final permutations start,end, and
updates as [event,index,prefix list] entries. index starts at zero within each
event. The result is a canonical actual reading or an obstruction. Crossings
are adjacent positions, updates are [event,index]. The interval is assumed
executable on its positive port diagram.
"""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import combinations, combinations_with_replacement, permutations
import json
from pathlib import Path

from semistrict_surface_private_histories import closure


def canonical(start,end,updates):
    start,end=tuple(start),tuple(end)
    if len(set(start))!=len(start) or set(start)!=set(end) or len(start)!=len(end):
        raise ValueError('expected two permutations of the same events')
    ids=set(updates)
    requirements={i:set() for i in ids}
    buckets={}
    for key,raw in updates.items():
        e,j=key
        s=set(raw)
        if e not in start or e in s or s-set(start) or j<0 or (j and (e,j-1) not in ids):
            raise ValueError('invalid checkpoint or nonconsecutive update indices')
        if j:
            requirements[key].add((e,j-1))
        buckets[key]={a:(1 if a==e else 0 if a in s else 2) for a in start}
    for a,b in combinations(start,2):
        early=[i for i,g in buckets.items() if g[a]<g[b]]
        late=[i for i,g in buckets.items() if g[a]>g[b]]
        if end.index(a)<end.index(b):
            if late:
                return None
        else:
            for i in late:
                requirements[i].update(early)
    p=list(start)
    answer=[]
    def sort_to(target):
        for i,x in enumerate(target):
            j=p.index(x)
            while j>i:
                assert end.index(x)<end.index(p[j-1])
                p[j-1],p[j]=p[j],p[j-1]
                answer.append(j-1)
                j-=1
    pending=set(ids)
    while pending:
        eligible=[i for i in pending if not requirements[i]&pending]
        if not eligible:
            return None
        i=min(eligible)
        sort_to(sorted(p,key=buckets[i].get))
        answer.append(i)
        pending.remove(i)
    sort_to(end)
    return tuple(answer)


def profiles(start,reading):
    p=list(start)
    out={}
    for token in reading:
        if isinstance(token,tuple):
            e,_=token
            out[token]=frozenset(p[:p.index(e)])
        else:
            p[token],p[token+1]=p[token+1],p[token]
    return tuple(p),out


def neighbors(start,w):
    p=list(start)
    for k,a in enumerate(w):
        if k+1<len(w):
            b=w[k+1]
            if isinstance(a,tuple) and isinstance(b,tuple):
                swap=a[0]!=b[0]
            elif isinstance(a,int) and isinstance(b,int):
                swap=abs(a-b)>1
            else:
                mark,j=(a,b) if isinstance(a,tuple) else (b,a)
                swap=p.index(mark[0]) not in (j,j+1)
            if swap:
                yield w[:k]+(b,a)+w[k+2:]
        if k+2<len(w):
            b,c=w[k+1:k+3]
            if a==c and isinstance(a,int) and isinstance(b,int) and abs(a-b)==1:
                yield w[:k]+(b,a,b)+w[k+3:]
        if isinstance(a,int):
            p[a],p[a+1]=p[a+1],p[a]


def readings(start,end,marks):
    def walks(p):
        if p==end:
            yield ()
        for j,(a,b) in enumerate(zip(p,p[1:])):
            if end.index(a)>end.index(b):
                for tail in walks(p[:j]+(b,a)+p[j+2:]):
                    yield (j,)+tail
    for w in walks(start):
        for order in set(permutations(marks)):
            seen=defaultdict(int)
            ids=[]
            for e in order:
                ids.append((e,seen[e]))
                seen[e]+=1
            for cuts in combinations_with_replacement(range(len(w)+1),len(ids)):
                yield tuple(step for j in range(len(w)+1)
                            for step in tuple(t for t,i in zip(ids,cuts) if i==j)+w[j:j+1])


def checks():
    count=components=impossible=0
    for n,marks,goal in [(3,(0,1,2),(2,1,0)),(3,(0,0,1),(2,1,0)),
                         (4,(0,1,2),(3,2,1,0)),(4,(1,3,3),(2,1,3,0))]:
        start=tuple(range(n))
        groups=defaultdict(set)
        for r in readings(start,goal,marks):
            end,p=profiles(start,r)
            assert end==goal
            groups[tuple(sorted(p.items()))].add(r)
        for key,group in groups.items():
            normal=canonical(start,goal,dict(key))
            assert normal in group and closure(normal,lambda w:neighbors(start,w))==group
        count+=sum(map(len,groups.values()))
        components+=len(groups)
        # Vary one checkpoint without assuming the mutated record is feasible.
        for key in groups:
            original=dict(key)
            for (e,i),s in key:
                for a in set(start)-{e}:
                    changed={**original,(e,i):s^{a}}
                    result=canonical(start,goal,changed)
                    expected=groups.get(tuple(sorted(changed.items())))
                    assert (result is None)==(not expected)
                    if result is None:
                        impossible+=1
                    else:
                        assert result in expected
    print(f'{count} readings, {components} exact reversible components, '
          f'{impossible} infeasible one-bit mutations rejected')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--checkpoints',type=Path)
    args=p.parse_args()
    if args.checkpoints:
        d=json.loads(args.checkpoints.read_text())
        answer=canonical(d['start'],d['end'],{(e,i):s for e,i,s in d['updates']})
        print(json.dumps({'realizable':answer is not None,'reading':answer}))
    else:
        checks()
