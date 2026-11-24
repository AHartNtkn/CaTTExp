"""Decide degree-four interchange comparisons in a simple interval with private updates on one event.

--interval FILE uses width, schedule ([offset,in,out]), start (permutation of
event indices), mark (event index), and two parallel lists source,target.
An integer swaps that adjacent pair in its native direction; each "P" is the
next positioned change on the marked event. Paths are old positive readings and must end in the same order.
"""
from argparse import ArgumentParser
from itertools import combinations_with_replacement
import json
from pathlib import Path

from semistrict_surface_planar_columns import Column
from semistrict_surface_planar_event_projection import cuts
from semistrict_surface_private_histories import closure


class Interval:
    def __init__(self,width,schedule,start,mark):
        col=Column(width,schedule)
        self.sites=cuts(col)[1]
        self.start=tuple(start)
        self.mark=mark
        if set(start)!=set(range(len(schedule))) or len(start)!=len(schedule) or mark not in start:
            raise ValueError('expected a permutation and one of its events')
        if any(e not in self.sites.get(frozenset(start[:i]),{}) for i,e in enumerate(start)):
            raise ValueError('initial order violates wire dependence')

    def exchange(self,order,j):
        if type(j)!=int or not 0<=j<len(order)-1:
            return None
        pos=self.sites[frozenset(order[:j])]
        a,b=order[j:j+2]
        if b not in pos or pos[a]<=pos[b]:
            return None
        return order[:j]+(b,a)+order[j+2:]

    def read(self,steps):
        p=self.start
        prefixes=[]
        for s in steps:
            if s=='P':
                prefixes.append(frozenset(p[:p.index(self.mark)]))
            else:
                p=self.exchange(p,s)
                if p is None:
                    raise ValueError('non-native adjacent exchange')
        return p,tuple(prefixes)

    def neighbors(self,steps,*,both_braids):
        # Direct presentation: strict commute, both pure cube hemispheres on
        # the surface, or one directed mixed prism relative to the mark.
        p=self.start
        for i,s in enumerate(steps):
            pair=steps[i:i+2]
            if len(pair)==2:
                a,b=pair
                if a==b=='P':
                    pass
                elif a=='P' or b=='P':
                    j=b if a=='P' else a
                    # Native prisms make the private event later in its
                    # instantaneous temporal list. Disjoint letters commute.
                    at=p.index(self.mark)
                    if at not in (j,j+1) or (a=='P' and at==j) or (b=='P' and at==j+1):
                        yield steps[:i]+(b,a)+steps[i+2:]
                elif abs(a-b)>1:
                    yield steps[:i]+(b,a)+steps[i+2:]
            triple=steps[i:i+3]
            if len(triple)==3 and 'P' not in triple:
                a,b,c=triple
                if a==c and (b==a+1 or (both_braids and b==a-1)):
                    yield steps[:i]+(b,a,b)+steps[i+3:]
            if s!='P':
                p=self.exchange(p,s)
                assert p is not None

    def readings(self,end,count):
        def walk(p):
            if p==end:
                yield ()
            for j in range(len(p)-1):
                q=self.exchange(p,j)
                if q is not None and end.index(p[j])>end.index(p[j+1]):
                    for w in walk(q):
                        yield (j,)+w
        for w in walk(self.start):
            for cuts_at in combinations_with_replacement(range(len(w)+1),count):
                yield tuple(step for i in range(len(w)+1)
                            for step in ('P',)*cuts_at.count(i)+w[i:i+1])


def solve(data):
    chart=Interval(data['width'],data['schedule'],data['start'],data['mark'])
    source,target=(tuple(data[k]) for k in ('source','target'))
    (s,u),(t,v)=chart.read(source),chart.read(target)
    if s!=t:
        raise ValueError('the two readings must have common temporal ends')
    return {'surface_filler':len(u)==len(v) and all(a<=b for a,b in zip(u,v)),
            'source_prefixes':list(map(sorted,u)),'target_prefixes':list(map(sorted,v))}


def checks():
    pure=[(i,1,1) for i in (3,2,1,0)]
    split=[(0,1,3),(2,1,1),(1,1,1),(0,1,1),(0,3,1)]
    cases=[(4,pure,p) for p in [(3,2,1,0),(3,1,2,0),(2,3,0,1)]]
    cases.append((1,split,(0,3,2,1,4)))
    total=surface=conversion=0
    multiple=0
    for width,sch,end in cases:
        for e in range(len(sch)):
            chart=Interval(width,sch,tuple(range(len(sch))),e)
            counts=(1,2) if end!=(3,2,1,0) else (1,)
            if width==1:
                counts=(1,2,3)
            for count in counts:
                prefixes={w:chart.read(w)[1] for w in chart.readings(end,count)}
                for w,u in prefixes.items():
                    found=closure(w,lambda s:chart.neighbors(s,both_braids=True))
                    raw=closure(w,lambda s:chart.neighbors(s,both_braids=False))
                    assert found=={v for v,p in prefixes.items() if all(a<=b for a,b in zip(u,p))} and raw<=found
                    total+=len(prefixes)
                    multiple+=len(prefixes) if count>1 else 0
                    surface+=len(found)
                    conversion+=len(found-raw)
    assert conversion
    print(f'{total} parallel decorated-reading pairs, {surface} surface-positive, '
          f'{conversion} surface-only; {multiple} comparisons with multiple private updates')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--interval',type=Path)
    args=p.parse_args()
    if args.interval:
        print(json.dumps(solve(json.loads(args.interval.read_text()))))
    else:
        checks()
