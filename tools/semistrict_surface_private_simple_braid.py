"""Decide private old degree-four comparisons in named simple braid sectors.

--faces FILE uses positioned histories from private_movies. A null answer
identifies a hypothesis outside this decision procedure.
"""
from argparse import ArgumentParser
from collections import defaultdict,deque
from itertools import permutations
import json
from pathlib import Path

from semistrict_surface_acyclic_private_movies import Traces, solve as trace_test
from semistrict_surface_history_group import exchange
from semistrict_surface_private_checkpoint_blocks import decide
from semistrict_surface_private_four_surface import Diagram
from semistrict_surface_private_histories import closure, solve as validate
from semistrict_surface_shared_edge import braid_image


def named_component(start,marks,updates):
    adjacent = defaultdict(set)
    for a,b in updates.values():
        adjacent[a].add(b)
        adjacent[b].add(a)
    shape = {a:min(closure(a,lambda x:adjacent[x])) for a in marks}
    h = tuple((pos,shape[a]) for pos,a in start)
    if len({a for _,a in h}) == len(h):
        return True
    names = {h:tuple(range(len(h)))}
    todo = deque(names)
    while todo:
        h = todo.popleft()
        for i in range(len(h)-1):
            p = names[h]
            q = p[:i]+(p[i+1],p[i])+p[i+2:]
            for letter in (i+1,-i-1):
                dest = exchange(h,letter,marks)
                if dest is not None:
                    if dest in names:
                        if names[dest] != q:
                            return False
                    else:
                        names[dest] = q
                        todo.append(dest)
    return True


class SimpleInterval(Diagram):
    def __init__(self,end):
        self.n = len(end)
        self.preds = [sum(1<<f for f in end[:end.index(e)] if f<e) for e in range(self.n)]

    def sites(self,s):
        return [e for e,p in enumerate(self.preds) if not (s >> e & 1 or p & ~s)]


def read(chart,start,steps):
    h = start
    order = list(range(len(h)))
    labels = {}
    counts = defaultdict(int)
    word,braid = [],[]
    simple = True
    for label,i in steps:
        if label=='X':
            if not 0<=i<len(h)-1 or (h:=exchange(h,i+1,chart.marks)) is None:
                raise ValueError('illegal positioned exchange')
            simple &= order[i]<order[i+1]
            order[i],order[i+1] = order[i+1],order[i]
            braid.append(i+1)
        else:
            h = chart.act(h,i,label)
            e = order[i]
            key = e,counts[e]
            labels[key] = label
            counts[e] += 1
            word.append((*key,sum(1<<x for x in order[:i])))
    return h,tuple(order),tuple(word),labels,braid,simple


def verify_interval_moves(start,marks,source,target,steps):
    n = len(start)
    def at(order):
        order = tuple(order)
        h,p = start,list(range(n))
        for i,e in enumerate(order):
            j = p.index(e)
            while j>i:
                h = exchange(h,j,marks)
                assert h is not None
                p[j],p[j-1] = p[j-1],p[j]
                j -= 1
        return h
    w = list(source)
    def events(mask):
        return [e for e in range(n) if mask>>e&1]
    full = (1<<n)-1
    for kind,k,*args in steps:
        e,j,s = w[k]
        if kind=='grow':
            x, = args
            tail = events(full & ~(s | 1<<e | 1<<x))
            before = events(s)+[e,x]+tail
            after = events(s)+[x,e]+tail
            edge = (s.bit_count()+1) * (1 if e<x else -1)
            assert exchange(at(before),edge,marks) == at(after)
            w[k] = (e,j,s | 1<<x)
        else:
            f,_,t = w[k+1]
            if (s | 1<<e) & ~t:
                e,s,f,t = f,t,e,s
            assert not (s | 1<<e) & ~t
            at(events(s)+[e]+events(t & ~(s | 1<<e))+[f]+events(full & ~(t | 1<<f)))
            w[k],w[k+1] = w[k+1],w[k]
    assert tuple(w)==target


def solve(data):
    start = tuple(map(tuple,data['history']))
    validate({**data,'source':start,'target':start})
    layers = data.get('higher',[])+[{},{}]
    if 'X' in layers[0]:
        raise ValueError('reserved exchange label')
    chart = Traces(data['marks'],*layers[:2])
    a,u,w,old,braid,simple = read(chart,start,data['source'])
    b,v,z,new,other,also_simple = read(chart,start,data['target'])
    if a!=b:
        raise ValueError('nonparallel old readings')
    if u!=v or (simple!=also_simple) or (not simple and braid_image(len(u),braid)!=braid_image(len(v),other)):
        return dict(surface_filler=False,obstruction='unequal erased braids')
    if not simple:
        return dict(surface_filler=None,outside='nonsimple braid')
    def obstruction(reason):
        if named_component(start,data['marks'],layers[0]) or trace_test(data)['surface_filler'] is False:
            return dict(surface_filler=False,obstruction=reason)
        return dict(surface_filler=None,outside='shape loop permutes occurrences')
    replacements = defaultdict(set)
    for p,q in layers[1].values():
        replacements[p].add(q)
    if old.keys()!=new.keys() or any(new[k] not in closure(p,lambda x:replacements[x]) for k,p in old.items()):
        return obstruction('positioned private labels')
    path,parts = decide(SimpleInterval(u),w,z)
    if path is None:
        return obstruction('prefix trace')
    verify_interval_moves(start,data['marks'],w,z,path)
    return dict(surface_filler=True,block_sizes=list(map(len,parts)),trace_moves=path)


def checks():
    from semistrict_surface_checkpoint_orders import readings
    start,end = (0,1,2),(2,1,0)
    marks = {a:('','') for a in 'abcABC'}
    h = tuple((0,a) for a in 'abc')
    updates = {a+'!':(a,a.upper()) for a in 'abc'}
    data = dict(edges={},scalar_at={a:0 for a in marks},marks=marks,higher=[updates],
                start_vertex=0,initial=[],history=h)
    chart = Traces(marks,updates,{})
    def movie(w):
        p = list(start)
        out = []
        for step in w:
            if isinstance(step,int):
                out.append(('X',step))
                p[step],p[step+1]=p[step+1],p[step]
            else:
                e,_ = step
                out.append(('abc'[e]+'!',p.index(e)))
        return out
    # On fully named scalar phases every swap is executable in both signs.
    # The positioned word criterion is an independent necessary lower bound.
    movies = {}
    for w in readings(start,end,start):
        m = movie(w)
        movies[chart.read(h,m)[1]] = m
    count = positive = 0
    for w,source in movies.items():
        reachable = closure(w,lambda x:(q for _,q in chart.next(x)))
        for z,target in movies.items():
            result = solve(dict(data,source=source,target=target))
            assert result['surface_filler'] == (z in reachable)
            positive += z in reachable
            count += 1
    # Test a proper interval where some pairs never cross, with an actual
    # nonempty spatial event beside a pair of floating scalar occurrences.
    data.update(edges={'x':[0,0]},initial=['x'],history=[(1,'a'),(1,'b'),(0,'c')])
    for a in 'cC':
        marks[a]=('x','x')
    for end in permutations(start):
        for w in readings(start,end,(0,2)):
            result=solve(dict(data,source=movie(w),target=movie(w)))
            assert result['surface_filler']
    repeat = dict(data,history=[(1,'a'),(1,'a')],source=[('a!',0),('X',0)],
                  target=[('X',0),('a!',1)])
    assert solve(repeat)['surface_filler']
    assert not named_component(((0,'a'),(0,'a')),marks,updates)
    assert named_component(((0,'c'),(0,'c')),marks,updates)
    print(f'{count} named cyclic scalar comparisons ({positive} positive) match positioned reachability; '
          'proper intervals, anchored sites and permutation isotropy checked')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--faces',type=Path)
    args=p.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()))))
    else:
        checks()
