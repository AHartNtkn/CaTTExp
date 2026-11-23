"""Search signed private movies in a finite ball of executable braid prefixes.

--faces FILE accepts positioned old degree-four readings. A positive answer
includes the moves. A negative finite-ball search can leave a larger query
open. The union over all radii realizes all signed movie comparisons.
"""
from argparse import ArgumentParser
from collections import defaultdict,deque
import json
from pathlib import Path

from semistrict_surface_acyclic_private_movies import Traces
from semistrict_surface_history_group import exchange
from semistrict_surface_private_histories import closure,solve as validate
from semistrict_surface_private_simple_braid import read
from semistrict_surface_shared_edge import braid_image


class Ball:
    def __init__(self,start,marks,radius):
        if radius<0:
            raise ValueError('expected nonnegative radius')
        n=len(start)
        ports={e:marks[a] for e,(_,a) in enumerate(start)}
        h=tuple((p,e) for e,(p,_) in enumerate(start))
        self.paths=[()]
        self.histories=[h]
        self.index={braid_image(n,()):0}
        self.edges=[]
        for here,path in enumerate(self.paths):
            edges=[]
            self.edges.append(edges)
            for j in range(1,n):
                for swap in (j,-j):
                    g=exchange(self.histories[here],swap,ports)
                    if g is None:
                        continue
                    extension=path+(swap,)
                    braid=braid_image(n,extension)
                    there=self.index.get(braid)
                    if there is None:
                        if len(extension)>radius:
                            continue
                        there=len(self.paths)
                        self.index[braid]=there
                        self.paths.append(extension)
                        self.histories.append(g)
                    assert self.histories[there]==g
                    edges.append((swap,there))

    def word(self,reading,trace):
        braid=[]
        moves=iter(trace)
        word=[]
        n=len(self.histories[0])
        for op,i in reading:
            if op=='X':
                braid.append(i+1)
            else:
                e,j,_=next(moves)
                node=self.index.get(braid_image(n,braid))
                if node is None:
                    return None
                assert self.histories[node][i][1]==e
                word.append((e,j,node))
        return tuple(word)

    def steps(self,w):
        for k,(e,j,h) in enumerate(w):
            i=next(p for p,(_,x) in enumerate(self.histories[h]) if x==e)
            for swap,g in self.edges[h]:
                if i!=abs(swap):
                    yield ('transport',k,swap),w[:k]+((e,j,g),)+w[k+1:]
            if k+1<len(w) and w[k+1][0]!=e and w[k+1][2]==h:
                yield ('commute',k),w[:k]+(w[k+1],w[k])+w[k+2:]

    def search(self,w,z):
        queue=deque([w])
        back={w:None}
        while queue:
            x=queue.popleft()
            if x==z:
                path=[]
                while back[x] is not None:
                    x,move=back[x]
                    path.append(move)
                return path[::-1]
            for move,y in self.steps(x):
                if y not in back:
                    back[y]=x,move
                    queue.append(y)
        return None


def solve(data,radius):
    h=tuple(map(tuple,data['history']))
    validate({**data,'source':h,'target':h})
    layers=data.get('higher',[])+[{},{}]
    if 'X' in layers[0]:
        raise ValueError('reserved exchange label')
    chart=Traces(data['marks'],*layers[:2])
    a,u,w,old,left,_=read(chart,h,data['source'])
    b,v,z,new,right,_=read(chart,h,data['target'])
    if a!=b:
        raise ValueError('nonparallel old readings')
    if u!=v or braid_image(len(h),left)!=braid_image(len(h),right):
        return dict(surface_filler=False,obstruction='erased braid')
    changes=defaultdict(set)
    for p,q in layers[1].values():
        changes[p].add(q)
    if old.keys()!=new.keys() or any(new[m] not in closure(p,lambda x:changes[x]) for m,p in old.items()):
        return dict(surface_filler=False,obstruction='named private labels')
    chart=Ball(h,data['marks'],radius)
    start,goal=(chart.word(data[k],t) for k,t in [('source',w),('target',z)])
    if start is None or goal is None:
        return dict(surface_filler=None,reason='old checkpoint outside ball')
    proof=chart.search(start,goal)
    if proof is not None:
        state=start
        for step in proof:
            state=dict(chart.steps(state))[step]
        assert state==goal
    return dict(surface_filler=True if proof is not None else None,trace_moves=proof,
                radius=radius,braid_vertices=len(chart.paths))


def checks():
    from semistrict_surface_checkpoint_orders import readings
    from semistrict_surface_private_four_surface import Diagram
    from semistrict_surface_private_winding import obstruction,signature
    base=dict(edges={},initial=[],start_vertex=0,scalar_at={'s':0},marks={'s':[[],[]]},
              higher=[{'p':['s','s']}],history=[(0,'s')]*3)
    ball=Ball(tuple(base['history']),base['marks'],3)
    diagram=Diagram(3,[(2,1,1),(1,1,1),(0,1,1)])
    classes={}
    for w in readings((0,1,2),(2,1,0),(0,1)):
        order=[0,1,2]
        movie=[]
        for token in w:
            if isinstance(token,int):
                movie.append(('X',token))
                order[token],order[token+1]=order[token+1],order[token]
            else:
                movie.append(('p',order.index(token[0])))
        trace=diagram.read((0,1,2),w)[1]
        classes[ball.word(movie,trace)]=trace
    count=0
    for source,trace in classes.items():
        reachable=closure(source,lambda w:(q for _,q in ball.steps(w)))
        for target,other in classes.items():
            assert (target in reachable)==(diagram.search(trace,other) is not None)
            count+=1
    h=((0,'s'),)*2
    ball=Ball(h,base['marks'],5)
    chart=Traces(base['marks'],base['higher'][0],{})
    pairs=0
    for length in range(1,6):
        records={}
        for gap in range(length+1):
            for i in (0,1):
                movie=[('X',0)]*gap+[('p',i)]+[('X',0)]*(length-gap)
                w=read(chart,h,movie)[2]
                records[ball.word(movie,w)]=signature(2,movie)
        for s,sa in records.items():
            reachable=closure(s,lambda w:(q for _,q in ball.steps(w)))
            for t,ta in records.items():
                assert (t in reachable)==(obstruction(sa,ta,{}) is None)
                pairs+=1
    print(f'{count} three-fold scalar simple-sector comparisons and {pairs} winding '
          'comparisons agree with independently computed answers')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--faces',type=Path)
    p.add_argument('--radius',type=int,default=3)
    args=p.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()),args.radius)))
    else:
        checks()
