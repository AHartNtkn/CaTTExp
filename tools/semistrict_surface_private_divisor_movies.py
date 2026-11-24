"""Decide private surface comparisons within one temporal gain per update.

All accepted divisor-interval paths are witnesses. Exhaustion is conclusive
if each update gains at most one preceding event, including at nonsimple braids.
"""
from argparse import ArgumentParser
from collections import defaultdict,deque
import json
from pathlib import Path

from semistrict_surface_acyclic_private_movies import Traces
from semistrict_surface_history_group import exchange
from semistrict_surface_one_step_reflection import quotient
from semistrict_surface_private_histories import closure,solve as validate
from semistrict_surface_private_simple_braid import read
from semistrict_surface_private_winding import obstruction,signature
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_signed_private_model import Ball


class Divisors(Ball):
    def __init__(self,start,marks,braid):
        n=len(start)
        ports={e:marks[label] for e,(_,label) in enumerate(start)}
        self.paths=[()]
        self.histories=[tuple((p,e) for e,(p,_) in enumerate(start))]
        self.edges=[[]]
        self.index={braid_image(n,()):0}
        for i,path in enumerate(self.paths):
            for j in range(1,n):
                w=path+(j,)
                if quotient(w,braid) is None:
                    continue
                key=braid_image(n,w)
                dest=exchange(self.histories[i],j,ports)
                assert dest is not None
                if key not in self.index:
                    self.index[key]=len(self.paths)
                    self.paths.append(w)
                    self.histories.append(dest)
                    self.edges.append([])
                k=self.index[key]
                assert self.histories[k]==dest
                self.edges[i].append((j,k))
                self.edges[k].append((-j,i))


def stationary(chart,start,goal):
    """Trace equality on the disjoint components of each marked checkpoint."""
    order={m[:2]:k for k,m in enumerate(goal)}
    target={m[:2]:m[2] for m in goal}
    cache={}
    classes=[]
    for e,j,node in start:
        def disjoint(h):
            i=next(k for k,(_,x) in enumerate(chart.histories[h]) if x==e)
            return (t for step,t in chart.edges[h] if abs(step) not in (i,i+1))
        if (e,node) not in cache:
            component=closure(node,disjoint)
            for k in component:
                cache[e,k]=component
        component=cache[e,node]
        if target[e,j] not in component:
            return False
        classes.append(component)
    for i,left in enumerate(start):
        for k in range(i+1,len(start)):
            right=start[k]
            if order[left[:2]]>order[right[:2]]:
                if left[0]==right[0] or classes[i].isdisjoint(classes[k]):
                    return False
    return True


def passive_interval(n,position,prefix,beta):
    allowed=[g for g in range(1,n) if g not in (position,position+1)]
    def peel(word):
        head=[]
        while True:
            for g in allowed:
                rest=quotient((g,),word)
                if rest is not None:
                    head.append(g)
                    word=rest
                    break
            else:
                return tuple(head),word
    _,low=peel(prefix[::-1])
    high,_=peel(quotient(prefix,beta))
    return low[::-1],prefix+high


def compact(n,beta,source,target,w,z):
    def checkpoints(reading,trace):
        prefix=[]
        marks=iter(trace)
        result={}
        for op,i in reading:
            if op=='X':
                prefix.append(i+1)
            else:
                key=next(marks)[:2]
                result[key]=(i,tuple(prefix))
        return result
    a,b=checkpoints(source,w),checkpoints(target,z)
    intervals={}
    stages={}
    def le(low,high):
        return quotient(low,high) is not None
    for key,(i,prefix) in a.items():
        j,end=b[key]
        first=passive_interval(n,i,prefix,beta)
        intervals[*key,0]=first
        stages[key]=j-i
        if j==i:
            if not le(first[0],end) or not le(end,first[1]):
                return False
        else:
            assert j==i+1
            second=passive_interval(n,j,end,beta)
            if not (le(first[0],second[1]) or le(second[0],first[1])):
                return False
            intervals[*key,1]=second
    def compatible(a,b):
        if a[0]==b[0]:
            return False
        s,t=intervals[a],intervals[b]
        return le(s[0],t[1]) and le(t[0],s[1])
    first=tuple((*m[:2],0) for m in w)
    last=tuple((*m[:2],stages[m[:2]]) for m in z)
    if first==last:
        return True
    if not any(stages.values()):
        order={m:i for i,m in enumerate(last)}
        return all(compatible(a,b) for i,a in enumerate(first) for b in first[i+1:] if order[a]>order[b])
    def steps(word):
        for k,(e,j,t) in enumerate(word):
            if t<stages[e,j]:
                yield word[:k]+((e,j,1),)+word[k+1:]
            if k+1<len(word) and compatible(word[k],word[k+1]):
                yield word[:k]+(word[k+1],word[k])+word[k+2:]
    todo=deque([first])
    seen={first}
    while todo:
        for state in steps(todo.popleft()):
            if state==last:
                return True
            if state not in seen:
                seen.add(state)
                todo.append(state)
    return False


def solve(data):
    h=tuple(map(tuple,data['history']))
    validate({**data,'source':h,'target':h})
    layers=data.get('higher',[])+[{},{}]
    if 'X' in layers[0]:
        raise ValueError('reserved exchange label')
    chart=Traces(data['marks'],*layers[:2])
    a,u,w,_,left,_=read(chart,h,data['source'])
    b,v,z,_,right,_=read(chart,h,data['target'])
    if a!=b:
        raise ValueError('nonparallel old readings')
    if u!=v or len(left)!=len(right) or quotient(tuple(left),tuple(right))!=():
        return dict(surface_filler=False,obstruction='erased braid')
    def old(steps):
        return [('X' if label=='X' else (label,),i) for label,i in steps]
    changes=defaultdict(set)
    for p,q in layers[1].values():
        changes[p,].add((q,))
    reason=obstruction(*(signature(len(h),old(data[k])) for k in ('source','target')),changes)
    if reason:
        return dict(surface_filler=False,obstruction=reason)
    goals={m[:2]:m[2] for m in z}
    gain=max(((goals[e,j]^s).bit_count() for e,j,s in w),default=0)
    if gain<=1:
        return dict(max_gain=gain,surface_filler=compact(len(h),tuple(left),data['source'],data['target'],w,z))
    chart=Divisors(h,data['marks'],tuple(left))
    start,goal=(chart.word(data[k],t) for k,t in [('source',w),('target',z)])
    assert start is not None and goal is not None
    result=dict(max_gain=gain,divisors=len(chart.paths))
    moves=chart.search(start,goal)
    if moves is not None:
        state=start
        for move in moves:
            state=dict(chart.steps(state))[move]
        assert state==goal
    return dict(result,surface_filler=True if moves is not None else None,
                trace_moves=moves)


def checks():
    from semistrict_surface_single_power import spellings
    h=((0,'s'),)*3
    data=dict(edges={},initial=[],start_vertex=0,scalar_at={'s':0},marks={'s':[[],[]]},
              higher=[{'p':['s','s']}],history=h)
    beta=(1,2,1,1,2,1)
    interval=Divisors(h,data['marks'],beta)
    ball=Ball(h,data['marks'],6)
    chart=Traces(data['marks'],data['higher'][0],{})
    classes={}
    for pure in spellings(beta):
        for first in range(0,7,2):
            for second in (first,6):
                for i in range(3):
                    for j in range(3):
                        movie=[('X',g-1) for g in pure]
                        movie.insert(second,('p',j))
                        movie.insert(first,('p',i))
                        w=read(chart,h,movie)[2]
                        classes[interval.word(movie,w)]=(ball.word(movie,w),w,movie)
    comparisons=equal=0
    for source,(outside,w,src_movie) in classes.items():
        inside=closure(source,lambda s:(q for _,q in interval.steps(s)))
        larger=closure(outside,lambda s:(q for _,q in ball.steps(s)))
        for goal,(other,z,dst_movie) in classes.items():
            wanted={m[:2]:m[2] for m in z}
            if any((e,j) not in wanted or s & ~wanted[e,j] for e,j,s in w):
                continue
            gain=max((wanted[e,j]^s).bit_count() for e,j,s in w)
            if gain<=1:
                assert (goal in inside)==(other in larger)
                assert solve(dict(data,source=src_movie,target=dst_movie))['surface_filler']==(goal in inside)
                comparisons+=1
                if gain==0:
                    assert stationary(interval,source,goal)==(goal in inside)
                    equal+=1
    # Same pair counts at a mark can hide noncommuting pure winding: the
    # two prefixes below are distinct pure braids with equal pair counts.
    a=[('X',0)]*2+[('X',1)]*2
    b=[('X',1)]*2+[('X',0)]*2
    from semistrict_surface_private_braid_windows import join,factor
    pa,pb=tuple(i+1 for _,i in a),tuple(i+1 for _,i in b)
    total=join(pa,pb)
    old=[]
    for path,prefix in ((a,pa),(b,pb)):
        old.append(path+[('p',1)]+[('X',g-1) for g in factor(prefix,total)])
    assert not obstruction(*(signature(3,w) for w in old),{})
    assert solve(dict(data,source=old[0],target=old[1]))['surface_filler'] is False
    print(f'{comparisons} comparisons agree across divisor and signed balls, including '
          f'{equal} stationary trace tests; a winding invisible to all pair counts is rejected')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--faces',type=Path)
    args=p.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()))))
    else:
        checks()
