"""Polynomial raw degree-four test for positioned private movies in simple braids.

--faces FILE uses the private_movies format. A comparable pair reports the
number of directed cube and prism occurrences needed before private relabelling.
"""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_acyclic_private_movies import Traces
from semistrict_surface_private_histories import closure,solve as validate
from semistrict_surface_private_simple_braid import read


def packets(n,braid):
    p = list(range(n))
    times = {}
    for t,g in enumerate(braid):
        a,b = p[g-1:g+1]
        if a>=b:
            raise ValueError('expected a simple positive braid')
        times[a,b] = t
        p[g-1:g+1] = b,a
    return {(a,b,c) for a,b,c in combinations(range(n),3)
            if (a,b) in times and (b,c) in times and times[b,c]<times[a,b]}


def records(word):
    return {m[:2]:m[2] for m in word}


def compare(w,z,lower,upper):
    if lower.keys()!=upper.keys() or any(s & ~upper[k] for k,s in lower.items()):
        return dict(raw_filler=False,obstruction='private checkpoint prefixes')
    if not w<=z:
        return dict(raw_filler=False,obstruction='pure packet order',triple=min(w-z))
    return dict(raw_filler=True,cubes=len(z-w),
                prisms=sum((upper[k]^s).bit_count() for k,s in lower.items()))


def solve(data):
    h = tuple(map(tuple,data['history']))
    validate({**data,'source':h,'target':h})
    layers = data.get('higher',[])+[{},{}]
    if 'X' in layers[0]:
        raise ValueError('reserved exchange label')
    chart = Traces(data['marks'],*layers[:2])
    a,u,w,old,braid,simple = read(chart,h,data['source'])
    b,v,z,new,other,also_simple = read(chart,h,data['target'])
    if a!=b:
        raise ValueError('nonparallel old readings')
    if u!=v or simple!=also_simple:
        return dict(raw_filler=False,obstruction='unequal erased braids')
    if not simple:
        return dict(raw_filler=None,outside='nonsimple braid')
    changes = defaultdict(set)
    for p,q in layers[1].values():
        changes[p].add(q)
    if old.keys()!=new.keys() or any(new[k] not in closure(p,lambda x:changes[x]) for k,p in old.items()):
        return dict(raw_filler=False,obstruction='named private labels')
    return compare(packets(len(h),braid),packets(len(h),other),records(w),records(z))


def cable(n,steps):
    """One central wire and one initially adjacent helper per successive private update."""
    p = list(range(n))
    counts = [0]*n
    for label,i in steps:
        if label=='X':
            p[i],p[i+1] = p[i+1],p[i]
        else:
            counts[p[i]] += 1
    bundles = [[(e,j) for j in range(k+1)] for e,k in enumerate(counts)]
    p = list(range(n))
    crossed = [0]*n
    braid = []
    for label,i in steps:
        e = p[i]
        base = sum(len(bundles[x]) for x in p[:i])
        if label=='X':
            f = p[i+1]
            for j in range(len(bundles[f])):
                for t in reversed(range(len(bundles[e]))):
                    braid.append(base+j+t+1)
            p[i],p[i+1]=p[i+1],p[i]
        else:
            braid.append(base+crossed[e]+1)
            crossed[e] += 1
    return sum(bundles,[]),braid


def checks():
    from semistrict_surface_checkpoint_orders import readings
    from semistrict_surface_positive_movies import moves
    compared=cabled=0
    for n,goal,marked in [(3,(2,1,0),(0,1,2)),(3,(2,1,0),(0,0,1)),
                          (4,(2,0,3,1),(0,2)),(4,(3,2,1,0),())]:
        h = tuple((0,'s') for _ in range(n))
        updates = {'p':('s','s')}
        chart = Traces({'s':('','')},updates,{})
        vals = {}
        for r in readings(tuple(range(n)),goal,marked):
            p = list(range(n))
            movie = []
            for step in r:
                if isinstance(step,int):
                    movie.append(('X',step))
                    p[step],p[step+1]=p[step+1],p[step]
                else:
                    movie.append(('p',p.index(step[0])))
            movie=tuple(movie)
            _,_,w,_,braid,_=read(chart,h,movie)
            wires,expanded=cable(n,movie)
            vals[movie] = (packets(n,braid), records(w), packets(len(wires),expanded))
        for src,(a,lower,first) in vals.items():
            accessible = closure(src,lambda w:(q for _,q in moves(h,w,{'p':(('s',),('s',))})))
            for dst,(b,upper,second) in vals.items():
                result=compare(a,b,lower,upper)
                assert result['raw_filler'] == (dst in accessible) == (first<=second)
                compared += 1
                cabled += 1
    # A full reversal followed by a private label change at a nonempty site,
    # with the other two strands scalars. The underlying twist is simple.
    data=dict(edges={'x':[0,0]},initial=['x'],scalar_at={'s':0},history=[(1,'s'),(1,'s'),(0,'a')],
              marks={'s':[[],[]],'a':[['x'],['x']]},
              higher=[{'p':['a','a'],'q':['a','a']},{'r':['p','q']}],
              source=[('X',0),('X',1),('X',0),('p',0)],
              target=[('X',1),('X',0),('X',1),('q',0)])
    assert solve(data)==dict(raw_filler=True,cubes=1,prisms=0)
    # One pair crosses twice: outside the simple decision, even with no marks.
    data['source']=data['target']=[('X',0),('X',0)]
    assert solve(data)['raw_filler'] is None
    n=20
    lex=[i for size in reversed(range(1,n)) for i in range(size)]
    labels=[('p',i) for i in range(n)]
    big=dict(edges={},initial=[],start_vertex=0,scalar_at={'s':0},marks={'s':[[],[]]},
             history=[(0,'s')]*n,higher=[{'p':['s','s']}],
             source=labels+[('X',i) for i in lex],
             target=labels+[('X',n-2-i) for i in lex])
    assert solve(big)==dict(raw_filler=True,cubes=1140,prisms=0)
    print(f'{compared} positioned raw comparisons agree with native movie closure and '
          f'{cabled} expanded packet tests, including repeated updates and proper intervals')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--faces',type=Path)
    args=p.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()))))
    else:
        checks()
