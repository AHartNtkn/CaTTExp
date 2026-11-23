"""Decide private-labelled old degree-three Gray judgments, including empty sites.

--histories FILE uses the base format of semistrict_surface_private_planar_spectrum
with initial (edge list), start_vertex when initial is empty, and source and
target as [offset,mark] lists. Returns raw and interchange-surface inhabitation.
"""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import product
import json
from pathlib import Path

from semistrict_surface_globular_judgment import reaches
from semistrict_surface_planar_layer_spectrum import presentation
from semistrict_surface_return_gaps import exchange_at


def neighbors(history,marks,both):
    for i in range(len(history)-1):
        native = exchange_at(history,i,marks)
        if native is not None:
            yield native
        if both:
            (p,a),(q,b) = history[i:i+2]
            s,t = marks[a]
            if p+len(t)<=q:
                yield history[:i]+((q+len(s)-len(t),b),(p,a))+history[i+2:]


def closure(initial,moves):
    seen,stack = {initial},[initial]
    while stack:
        for nxt in moves(stack.pop()):
            if nxt not in seen:
                seen.add(nxt)
                stack.append(nxt)
    return seen


def decide(source,target,marks,updates):
    if source==target:
        return True,True
    if len(source)!=len(target):
        return False,False
    graph = defaultdict(set)
    for a,b in updates:
        graph[a].add(b)
    possible = [{b for _,b in target if reaches(graph,a,b)} for _,a in source]
    frozen = [marks[a] for _,a in source]
    initial = tuple((p,i) for i,(p,_) in enumerate(source))
    def accepts(both):
        return any(all(p==q and b in possible[i] for (p,i),(q,b) in zip(h,target))
                   for h in closure(initial,lambda h:neighbors(h,frozen,both)))
    raw = accepts(False)
    return raw,raw or accepts(True)


def solve(data):
    presentation(data,allow_empty=True)
    marks,edges = data['marks'],data['edges']
    initial = data['initial']
    if any(edges[a][1]!=edges[b][0] for a,b in zip(initial,initial[1:])):
        raise ValueError('noncomposable initial edge path')
    v = edges[initial[0]][0] if initial else data['start_vertex']
    def replay(h):
        path = list(initial)
        for pos,a in h:
            s,t = marks[a]
            if pos<0 or pos>len(path) or path[pos:pos+len(s)]!=list(s):
                raise ValueError('mark does not fit the spatial word')
            here = v if pos==0 else edges[path[pos-1]][1]
            p = s or t
            want = edges[p[0]][0] if p else data['scalar_at'][a]
            if here!=want:
                raise ValueError('mark at wrong vertex')
            path[pos:pos+len(s)] = t
        return path
    source,target = (tuple(map(tuple,data[k])) for k in ('source','target'))
    if replay(source)!=replay(target):
        raise ValueError('histories have different final paths')
    updates = data.get('higher',[])
    raw,surface = decide(source,target,marks,updates[0].values() if updates else [])
    return {'raw_filler':raw,'interchange_surface_filler':surface}


def checks():
    marks = {f'{i}{j}':('x'*s,'x'*t) for i,(s,t) in enumerate(product(range(3),repeat=2))
             for j in range(2)}
    updates = [(a,a[0]+'1') for a in marks if a[1]=='0']
    updates += [(b,a) for a,b in updates if int(a[0])%2==0]
    def moves(h,both):
        yield from neighbors(h,marks,both)
        for i,(p,x) in enumerate(h):
            for a,b in updates:
                if x==a:
                    yield h[:i]+((p,b),)+h[i+1:]
    checks = positive = 0
    for a,b,gap in product(marks,marks,range(3)):
        s,t = marks[a]
        source = ((0,a),(len(t)+gap,b))
        target = ((len(s)+gap,b),(0,a))
        raw,surf = decide(source,target,marks,updates)
        expected = not (gap or s or t or marks[b][0] or marks[b][1])
        assert raw==expected==(target in closure(source,lambda h:moves(h,False))) and surf
        checks += 1
        positive += raw
    wider = 0
    for src in [((0,'00'),(0,'10'),(0,'30')),((1,'40'),(0,'40'),(0,'00')),
                ((0,'30'),(0,'10'),(1,'20')),((0,'00'),)*4]:
        universe = closure(src,lambda h:moves(h,True))
        forward = closure(src,lambda h:moves(h,False))
        for goal in universe:
            assert decide(src,goal,marks,updates)==(goal in forward,True)
            wider += 1
    from semistrict_surface_private_planar_spectrum import solve as spectrum
    scalars = {'edges':{},'marks':{'a':[[],[]],'b':[[],[]]},'scalar_at':{'a':0,'b':0},
               'higher':[{'u':['a','b']}]}
    assert spectrum(scalars)=={'failing_from':4}
    assert spectrum({**scalars,'edges':{'f':[0,0]}})=={'failing_from':3}
    assert spectrum({**scalars,'edges':{'f':[0,1]}})=={'failing_from':4}
    birth = {'edges':{'f':[0,0]},'marks':{'a':[[],['f']],'b':[[],['f']]},
             'higher':[{'u':['a','b']}]}
    assert spectrum(birth)=={'failing_from':3}
    assert solve({**birth,'initial':[],'start_vertex':0,'source':[[0,'a'],[1,'b']],
                  'target':[[0,'b'],[0,'a']]})=={'raw_filler':False,'interchange_surface_filler':True}
    print(f'{checks} bare returns ({positive} positive), {wider} labelled multi-event comparisons '
          'against literal reachability; scalar and birth spectra verified')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--histories',type=Path)
    args=p.parse_args()
    if args.histories:
        print(json.dumps(solve(json.loads(args.histories.read_text()))))
    else:
        checks()
