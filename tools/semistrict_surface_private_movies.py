"""Decide positioned degree-four raw movies with private labels on arbitrary sites.

--faces FILE accepts the base and initial spatial path of the private-history
solver, a starting temporal history 'history' ([offset,2-label] entries), and
'source','target' 2-readings ([3-label,event offset] entries; X means swap).
"""
from argparse import ArgumentParser
from collections import Counter, deque
from itertools import permutations, product
import json
from pathlib import Path

from gray_globe_comparison import atom
from semistrict_surface_planar_layer_spectrum import presentation
from semistrict_surface_positive_movies import moves, solve as scalar_solve
from semistrict_surface_private_histories import solve as check_history
from semistrict_surface_return_gaps import exchange_at


def movies(history,source,target,marks,updates,changes):
    if 'X' in updates:
        raise ValueError('X is reserved for a native crossing')
    rules = {name:((a,),(b,)) for name,(a,b) in updates.items()}
    def run(reading):
        current = history
        for name,i in reading:
            if name=='X':
                if not 0<=i<len(current)-1:
                    return None
                current = exchange_at(current,i,marks)
                if current is None:
                    return None
            else:
                a,b = updates[name]
                if not 0<=i<len(current) or current[i][1]!=a:
                    return None
                current = current[:i]+((current[i][0],b),)+current[i+1:]
        return current
    first,last = run(source),run(target)
    if first is None or last is None or first!=last:
        raise ValueError('expected parallel executable face readings')
    def profile(r):
        return (sum(c=='X' for c,_ in r),sum(c!='X' for c,_ in r))
    if profile(source)!=profile(target):
        return None
    # The two profile counts persist along every step. This search needs no
    # bound on repetitions of a private move. The state space itself is finite.
    previous={source:None}
    queue=deque([source])
    def steps(r):
        yield from moves(history,r,rules)
        for i,(name,at) in enumerate(r):
            for change,(a,b) in changes.items():
                if name==a:
                    yield change,r[:i]+((b,at),)+r[i+1:]
    while queue:
        p=queue.popleft()
        if p==target:
            result=[]
            while previous[p] is not None:
                parent,label=previous[p]
                result.append((label,p))
                p=parent
            return result[::-1]
        for label,q in steps(p):
            if q not in previous and run(q)==last:
                previous[q]=(p,label)
                queue.append(q)
    return None


def solve(data):
    presentation(data,allow_empty=True)
    h=tuple(map(tuple,data['history']))
    check_history({**data,'source':h,'target':h})
    src,dst=(tuple(map(tuple,data[k])) for k in ('source','target'))
    higher=data.get('higher',[])+[{},{}]
    answer=movies(h,src,dst,data['marks'],higher[0],higher[1])
    return {'raw_filler':answer is not None,'steps':answer}


def checks():
    # Compute both signed hemispheres of actual globe tensors, grouping native
    # facets by their ordered positive-dimensional factor ranks.
    charts=0
    for width in range(1,6):
        for ds in product(range(1,5),repeat=width):
            k=sum(ds)
            if not 2<=k<=10:
                continue
            sides=atom(tuple((d,2) for d in ds))[-2]
            counts=[Counter(tuple(d for d,_ in w if d) for w in side) for side in sides]
            expected=Counter(tuple(x for x in ds[:i]+(d-1,)+ds[i+1:] if x) for i,d in enumerate(ds))
            assert counts[0]==counts[1]==expected and len(sides[0])==width
            charts+=1
    updates={'p':('a','a'),'q':('a','a')}
    changes={'up':('p','q'),'down':('q','p')}
    marks={'a':('','')}
    h=((0,'a'),)*2
    readings=[tuple((n,i) for n,i in zip(names,places))
              for names in set(permutations(('X','p','p')))
              for places in product(*[(0,) if n=='X' else (0,1) for n in names])]
    comparisons=0
    for a,b in product(readings,repeat=2):
        native=movies(h,a,b,marks,{'p':('a','a')},{})
        independent=scalar_solve('aa',a,b,{'p':('a','a')})
        assert (native is not None)==(independent is not None)
        alternate=tuple(('q' if n=='p' else n,i) for n,i in b)
        assert (movies(h,a,alternate,marks,updates,changes) is not None)==(native is not None)
        comparisons+=1
    # Each prism fits on a real birth and death site in the directed order.
    marks={'a':('x',''),'b':('','x')}
    updates={'p':('a','a'),'q':('a','a')}
    h=((1,'a'),(0,'b'))
    s,t=(('p',0),('X',0)),(('X',0),('q',1))
    assert movies(h,s,t,marks,updates,{'ren':('p','q')}) is not None
    assert movies(h,t,s,marks,updates,{'ren':('p','q')}) is None
    # Parallel scalar loops give infinitely many fillers but finite search.
    assert movies(((0,'a'),),(('p',0),),(('q',0),),marks,updates,changes) is not None
    print(f'{charts} signed tensor profiles through local rank ten, {comparisons} movie pairs '
          'with and without cyclic changes, and positioned birth/death prism checked')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--faces',type=Path)
    args=p.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()))))
    else:
        checks()
