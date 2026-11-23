"""Decide the degree-four interchange surface on a named private planar diagram.

--comparison FILE specifies width,schedule,start as in the planar event solver.
In source,target use an integer for a native adjacent exchange and [event,index]
for a positioned private update (indices start at zero on each event). This
is the normalized common ordinary shape; directed private label reachability
is a separate test when the end labels differ.
"""
from argparse import ArgumentParser
from collections import defaultdict,deque
from itertools import permutations,product
import json
from pathlib import Path

from semistrict_surface_checkpoint_orders import readings
from semistrict_surface_planar_columns import Column
from semistrict_surface_planar_event_projection import cuts
from semistrict_surface_private_histories import closure


class Diagram:
    def __init__(self,width,schedule):
        _,sites=cuts(Column(width,schedule))
        self.sites={sum(1<<e for e in done):pos for done,pos in sites.items()}
        self.n=len(schedule)

    def legal(self,e,mask):
        return e in self.sites.get(mask,{})

    def read(self,start,steps):
        p=list(start)
        if sorted(p)!=list(range(self.n)):
            raise ValueError('start must name all event indices')
        done=0
        for e in p:
            if not self.legal(e,done):
                raise ValueError('start violates wire dependence')
            done|=1<<e
        counts=defaultdict(int)
        out=[]
        for token in steps:
            if type(token)==int:
                if not 0<=token<self.n-1:
                    raise ValueError('invalid exchange position')
                a,b=p[token:token+2]
                pos=self.sites[sum(1<<x for x in p[:token])]
                if b not in pos or pos[a]<=pos[b]:
                    raise ValueError('exchange is not native at its sites')
                p[token:token+2]=b,a
            else:
                e,i=token
                if i!=counts[e]:
                    raise ValueError('private indices must follow the order on each event')
                counts[e]+=1
                out.append((e,i,sum(1<<j for j in p[:p.index(e)])))
        return tuple(p),tuple(out)

    def steps(self,w,limits=None):
        for i,(e,j,s) in enumerate(w):
            if i+1<len(w):
                f,_,t=w[i+1]
                if (s|1<<e)&~t==0 or (t|1<<f)&~s==0:
                    yield ('commute',i),w[:i]+(w[i+1],w[i])+w[i+2:]
            for x in self.sites[s]:
                if x!=e and not s&(1<<x):
                    extra=s|1<<x
                    if self.legal(e,extra) and (limits is None or extra&~limits[e,j]==0):
                        yield ('grow',i,x),w[:i]+((e,j,extra),)+w[i+1:]

    def search(self,w,v):
        limits={(e,j):s for e,j,s in v}
        if set(limits)!={(e,j) for e,j,_ in w} or any(s&~limits[e,j] for e,j,s in w):
            return None
        previous={w:None}
        queue=deque([w])
        while queue:
            p=queue.popleft()
            if p==v:
                answer=[]
                while previous[p] is not None:
                    p,step=previous[p]
                    answer.append(step)
                return answer[::-1]
            for step,q in self.steps(p,limits):
                if q not in previous:
                    previous[q]=p,step
                    queue.append(q)
        return None


def solve(data):
    d=Diagram(data['width'],data['schedule'])
    (a,w),(b,v)=(d.read(data['start'],data[k]) for k in ('source','target'))
    if a!=b:
        raise ValueError('expected parallel readings')
    witness=d.search(w,v)
    return {'surface_filler':witness is not None,'trace_moves':witness}


def checks():
    # Independent signed-transport states store a whole actual temporal
    # permutation at each private update, permitting arbitrary pure transports
    # between them. Only adjacent real transpositions and coincident readings
    # at the two updates are used to generate the physical elementary moves.
    pairs=signed=0
    for width,schedule,marks in [(3,[(0,1,1),(1,1,1),(2,1,1)],(0,2)),
                                 (2,[(0,1,2),(0,1,1),(2,1,1)],(1,2))]:
        diag=Diagram(width,schedule)
        orders=[]
        for p in permutations(range(len(schedule))):
            if all(diag.legal(e,sum(1<<x for x in p[:i])) for i,e in enumerate(p)):
                orders.append(p)
        def trace(state):
            return tuple((e,0,sum(1<<x for x in p[:p.index(e)])) for e,p in state)
        def physical(state):
            for j,(e,p) in enumerate(state):
                for i in range(len(p)-1):
                    q=p[:i]+(p[i+1],p[i])+p[i+2:]
                    if q in orders and q.index(e)>=p.index(e):
                        yield state[:j]+((e,q),)+state[j+1:]
            if state[0][1]==state[1][1]:
                yield state[::-1]
        for order in permutations(marks):
            for perms in product(orders,repeat=2):
                state=tuple(zip(order,perms))
                actual={trace(s) for s in closure(state,physical)}
                expected=closure(trace(state),lambda w:(v for _,v in diag.steps(w)))
                assert actual==expected
                signed+=len(closure(state,physical))
                pairs+=1
    # Compare on all actual old readings of a three-colour reversal carrying
    # three independent updates, including paths with a different mark order.
    diag=Diagram(3,[(2,1,1),(1,1,1),(0,1,1)])
    words=list(readings((0,1,2),(2,1,0),(0,1,2)))
    traces=[diag.read((0,1,2),w)[1] for w in words]
    total=positive=0
    for src in set(traces):
        actual=closure(src,lambda w:(v for _,v in diag.steps(w)))
        for dst in set(traces):
            path=diag.search(src,dst)
            assert (path is not None)==(dst in actual)
            if path is not None:
                cur=src
                for step in path:
                    cur=dict(diag.steps(cur))[step]
                assert cur==dst
        m=traces.count(src)
        total+=m*len(traces)
        positive+=m*sum(t in actual for t in traces)
    print(f'{pairs} signed checkpoint configurations, {signed} physically reachable ordered '
          f'pairs, {total} old reading comparisons ({positive} surface-positive)')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--comparison',type=Path)
    args=p.parse_args()
    if args.comparison:
        print(json.dumps(solve(json.loads(args.comparison.read_text()))))
    else:
        checks()
