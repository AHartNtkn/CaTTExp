"""Decide private degree-four surface comparisons on acyclic exchange components.

--faces FILE uses the positioned history and movie format of private_movies.
A null answer means the shape component has braid loops and only the necessary
finite trace test passed. A failed trace test is an obstruction on any base.
"""
from argparse import ArgumentParser
from collections import defaultdict,deque
from itertools import product
import json
from pathlib import Path

from semistrict_surface_history_group import exchange
from semistrict_surface_private_histories import closure,solve as check_history


def acyclic(history,marks,updates):
    adj=defaultdict(set)
    for a,b in updates.values():
        adj[a].add(b)
        adj[b].add(a)
    name={a:min(closure(a,lambda x:adj[x])) for a in marks}
    start=tuple((p,name[a]) for p,a in history)
    def steps(h):
        for i in range(1,len(h)):
            for letter in (i,-i):
                q=exchange(h,letter,marks)
                if q is not None:
                    yield q
    component=closure(start,steps)
    forward={h:{q for i in range(1,len(h)) if (q:=exchange(h,i,marks)) is not None}
             for h in component}
    indegree=dict.fromkeys(component,0)
    for succ in forward.values():
        for q in succ:
            indegree[q]+=1
    pending=[h for h in component if not indegree[h]]
    count=0
    while pending:
        h=pending.pop()
        count+=1
        for q in forward[h]:
            indegree[q]-=1
            if not indegree[q]:
                pending.append(q)
    return count==len(component)


class Traces:
    def __init__(self,marks,updates,changes):
        self.marks,self.updates,self.changes=marks,updates,changes

    def act(self,h,i,p):
        a,b=self.updates[p]
        if not 0<=i<len(h) or h[i][1]!=a:
            raise ValueError('private change does not fit')
        return h[:i]+((h[i][0],b),)+h[i+1:]

    def read(self,h,reading):
        w=[]
        for name,i in reading:
            if name=='X':
                if not 0<=i<len(h)-1 or (h:=exchange(h,i+1,self.marks)) is None:
                    raise ValueError('illegal native exchange')
            else:
                w.append((h,i,name))
                h=self.act(h,i,name)
        return h,tuple(w)

    def next(self,w):
        for k,(h,i,p) in enumerate(w):
            for j in range(len(h)-1):
                if i==j+1:
                    continue
                for letter in (j+1,-j-1):
                    changed=exchange(h,letter,self.marks)
                    if changed is not None:
                        index=i+int(i==j)
                        yield ('increase' if i==j else 'disjoint',k,letter),w[:k]+((changed,index,p),)+w[k+1:]
            for name,(a,b) in self.changes.items():
                if a==p:
                    yield ('relabel',k,name),w[:k]+((h,i,b),)+w[k+1:]
            if k+1<len(w):
                g,j,q=w[k+1]
                if i!=j and self.act(h,i,p)==g:
                    two=((h,j,q),(self.act(h,j,q),i,p))
                    yield ('commute',k),w[:k]+two+w[k+2:]

    def search(self,start,goal):
        if len(start)!=len(goal):
            return None
        limit=sum(i for _,i,_ in goal)
        todo=deque([start])
        back={start:None}
        while todo:
            w=todo.popleft()
            if w==goal:
                out=[]
                while back[w] is not None:
                    w,tag=back[w]
                    out.append(tag)
                return out[::-1]
            if sum(i for _,i,_ in w)>limit:
                continue
            for tag,nxt in self.next(w):
                if nxt not in back:
                    back[nxt]=w,tag
                    todo.append(nxt)
        return None


def solve(d):
    h=tuple(map(tuple,d['history']))
    check_history({**d,'source':h,'target':h})
    layers=d.get('higher',[])+[{},{}]
    if 'X' in layers[0]:
        raise ValueError('X is reserved for exchanges')
    chart=Traces(d['marks'],layers[0],layers[1])
    (a,w),(b,z)=(chart.read(h,d[k]) for k in ('source','target'))
    if a!=b:
        raise ValueError('nonparallel readings')
    thin=acyclic(h,d['marks'],layers[0])
    proof=chart.search(w,z)
    return dict(acyclic_component=thin,surface_filler=False if proof is None else (True if thin else None),
                trace_moves=proof)


def checks():
    # Fully positioned births-only and deaths-only sites. Give each event a
    # distinct updatable phase and compare all readings with the ideal solver
    # on a separate three-column chart having the same physical order.
    from semistrict_surface_checkpoint_orders import readings
    from semistrict_surface_private_four_surface import Diagram
    diag=Diagram(3,[(2,1,1),(1,1,1),(0,1,1)])
    u=(0,1,2)
    bare=list(readings(u,u[::-1],(0,2)))
    total=0
    for source,target,h in [('x','',((2,'a'),(1,'b'),(0,'c'))),
                            ('','x',((2,'a'),(1,'b'),(0,'c')))]:
        marks={n:(source,target) for n in 'abcABC'}
        updates={'p':('a','A'),'q':('c','C')}
        chart=Traces(marks,updates,{})
        assert acyclic(h,marks,updates)
        def movie(r):
            order=list(u)
            out=[]
            for c in r:
                if isinstance(c,int):
                    out.append(('X',c))
                    order[c],order[c+1]=order[c+1],order[c]
                else:
                    e,_=c
                    out.append((('p' if e==0 else 'q'),order.index(e)))
            return out
        values=[(chart.read(h,movie(r))[1],diag.read(u,r)[1]) for r in bare]
        for x,y in values:
            real=closure(x,lambda w:(q for _,q in chart.next(w)))
            ideal=closure(y,lambda w:(q for _,q in diag.steps(w)))
            for v,w in values:
                assert (v in real)==(w in ideal)
                total+=1
    # Different updates can have the very same two old faces.
    d={'edges':{'x':[0,0]},'marks':{'a':[[],['x']],'A':[[],['x']]},
       'higher':[{'p':['a','A'],'q':['a','A']},{'change':['p','q']}],
       'initial':[],'start_vertex':0,'history':[[0,'a']],'source':[['p',0]],'target':[['q',0]]}
    assert solve(d)['surface_filler'] is True
    d['source'],d['target']=d['target'],d['source']
    assert solve(d)['surface_filler'] is False
    assert not acyclic(((0,'a'),(0,'a')),{'a':('','')},{})
    print(f'{total} positioned birth/death comparisons agree with independent-cut search; '
          'directed fourth-label choices and the scalar cycle detected')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--faces',type=Path)
    args=p.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()))))
    else:
        checks()
