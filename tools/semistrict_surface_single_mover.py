"""Group every gain of the unique moving polygon, allowing arbitrary stationary polygons."""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from semistrict_surface_packet_meetings import compatible
from semistrict_surface_signed_width_two import Movies,Presentation,Rule


def reorder(calc,movie,order):
    original=tuple(p for p,_ in movie[0])
    operations=[]
    for j,p in enumerate(order):
        k=original.index(p)
        while k>j:
            q=original[k-1]
            movie=calc.exchange(movie,k-1)
            if movie is None:
                return None,[]
            operations.append(('meet',q,p))
            original=original[:k-1]+(p,q)+original[k+1:]
            k-=1
    return movie,operations


def solve(calc,start,goal,initial,final,p,radius=None):
    from semistrict_surface_gain_runs import run
    first=tuple(q for q,_ in start[0])
    last=tuple(q for q,_ in goal[0])
    still=tuple(q for q in first if q!=p)
    goal_prefix=calc.scan(goal)[1][p][0]
    def no(reason,tried=0):
        return dict(surface=False,single_mover=p,central_orders=tried,obstruction=reason)
    # Nonexchangeable stationary pairs keep their order at every stage.
    dependent=[]
    for j,q in enumerate(still):
        for r in still[j+1:]:
            if not compatible(initial[q],initial[r]):
                if last.index(q)>last.index(r):
                    return no('stationary polygons require an unavailable meeting')
                dependent.append((q,r))
    choices=[]
    for q in still:
        sides={False,True}
        for order,cuts in ((first,initial),(last,final)):
            if not compatible(cuts[p],cuts[q]):
                sides&={order.index(q)<order.index(p)}
        if not sides:
            return no('no common placement for the gain run')
        choices.append(sorted(sides))
    unknown=False
    tried=0
    for bits in product(*choices):
        before={q for q,v in zip(still,bits) if v}
        if any(r in before and q not in before for q,r in dependent):
            continue
        order=tuple(q for q in still if q in before)+(p,)+tuple(q for q in still if q not in before)
        a,arrive=reorder(calc,start,order)
        b,depart=reorder(calc,goal,order)
        assert a is not None and b is not None
        candidate,bounded=run(calc,a,order.index(p),goal_prefix,final[p],radius)
        tried+=1
        unknown|=bounded
        if candidate is not None:
            return dict(surface=True,single_mover=p,central_orders=tried,
                        actions=arrive+[('run',p)]+[(op,r,q) for op,q,r in reversed(depart)])
    if unknown:
        return dict(surface=None,single_mover=p,central_orders=tried,reason='private transport radius')
    return no('no stationary order admits the gain run',tried)


def critical_order(path,stationary,chronologies,mover):
    """Construct a common execution order from native gains with known full cuts."""
    from semistrict_surface_meridian_transport import prod,quasi
    from semistrict_surface_history_group import inv
    def below(left_end,right_start):
        return quasi(prod(inv(left_end),right_start))
    intervals={}
    for q,t in stationary.items():
        sides=[]
        for a,b in zip(path,path[1:]):
            left=below(t.after,a.before)
            right=below(b.after,t.before)
            assert not (left and right)
            sides.append(-1 if right else 1 if left else 0)
        assert sorted(sides)==sides
        active=[k for k,x in enumerate(sides) if x==0]
        if not active:
            assert len(set(sides))==1
            active=[0 if sides[0]==1 else len(sides)-1]
        intervals[q]=active[0],active[-1]
    before=set()
    for q,(a,b) in intervals.items():
        values={o.index(q)<o.index(mover) for o in chronologies[a:b+1]}
        assert len(values)==1
        if values=={True}: before.add(q)
    static=[q for q in chronologies[0] if q!=mover]
    return tuple(q for q in static if q in before)+(mover,)+tuple(q for q in static if q not in before)


def checks():
    from random import Random
    from semistrict_surface_gain_runs import decide
    from semistrict_surface_link_schedules import decide as counts
    from semistrict_surface_packet_meetings import cut
    from semistrict_surface_phase_gains import decide as phases
    from semistrict_surface_scalar_meetings import hurwitz
    from semistrict_surface_raw_movie_graph import raw_compare,steps
    from semistrict_surface_polygon_cabling import rectangle
    from semistrict_surface_shared_edge import braid_image
    def example(slot,path):
        s=((slot,'s'),)
        private=Rule('',((0,'s'),),((0,'s'),))
        return Movies(Presentation({'f':(0,0)},{'s':('',''),'b':('','f'),'d':('f','')},
                      [Rule(path,s,((slot,'b'),(slot,'d'))),private,private],{'s':0,'b':0}),path),s*3
    x=steps((1,0,1))+((0,0),(2,2),(1,3))+steps(rectangle(0,2,2))
    y=steps((0,1))+((1,2),('swap',0),(2,1))+steps((0,1))+((0,2),)
    m,h=example(0,'')
    yes=decide(m,h,x,y)
    assert yes['surface'] and not yes['endpoints_forced'] and len(yes['actions'])==4
    assert not raw_compare(m,h,x,y)['raw'] and phases(m,h,x,y,True)['surface'] is None
    assert counts(m,h,x,y)['surface'] is None
    m,h=example(1,'f')
    no=decide(m,h,x,y)
    assert no['surface'] is False and not no['endpoints_forced']

    rng=Random(7325)
    stages=changed=protected=0
    for sample in range(600):
        n=rng.randrange(4,8)
        width=rng.randrange(1,min(3,n-2)+1)
        i=rng.randrange(n-width-1)
        frame=braid_image(n,tuple(rng.choice((-1,1))*rng.randrange(1,n) for _ in range(3)))
        banks=[frame]
        path=[cut(frame,i,width)]
        merged=[]
        for _ in range(rng.randrange(2,n-i-width+1)):
            exterior=[j for j in range(1,n) if j<i or j>i+width]
            for _ in range(rng.randrange(3) if exterior else 0):
                g=rng.choice(exterior)
                frame=hurwitz(frame,g-1,rng.choice((True,False)))
            banks.append(frame)
            merged.append(cut(frame,i,width+1))
            positive=rng.choice((True,False))
            for j in reversed(range(i,i+width)):
                frame=hurwitz(frame,j,positive)
            i+=1
            banks.append(frame)
            path.append(cut(frame,i,width))
        static={}
        for q in range(1,rng.randrange(4,7)):
            f=rng.choice(banks)
            for _ in range(rng.randrange(3)):
                f=hurwitz(f,rng.randrange(n-1),rng.choice((True,False)))
            size=rng.randrange(1,min(3,n)+1)
            static[q]=cut(f,rng.randrange(n-size+1),size)
        def walk(order,p):
            cuts={**static,0:p}
            order=list(order)
            for _ in range(24):
                j=rng.randrange(len(order)-1)
                a,b=order[j:j+2]
                if compatible(cuts[a],cuts[b]):
                    order[j:j+2]=b,a
            return tuple(order)
        def fits(a,b,p):
            cuts={**static,0:p}
            return all(compatible(cuts[q],cuts[r]) for j,q in enumerate(a)
                       for r in a[j+1:] if b.index(q)>b.index(r))
        order=list(range(1+len(static)))
        rng.shuffle(order)
        start=tuple(order)
        chronology=[]
        for c in path[:-1]:
            order=walk(order,c)
            chronology.append(order)
        end=walk(order,path[-1])
        central=critical_order(path,static,chronology,0)
        assert fits(start,central,path[0]) and fits(end,central,path[-1])
        for order,contact in zip(chronology,merged):
            assert fits(order,central,contact)
            changed+=order!=central
            protected+=any(not compatible(contact,q) for q in static.values())
            stages+=1
    assert changed and protected
    return dict(three_polygons=yes,padded_negative=no,signed_schedules=600,protected_gains=stages,
                reordered_gains=changed,gains_with_a_dependent_stationary_box=protected)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    args=parser.parse_args()
    if args.query:
        from semistrict_surface_gain_runs import decide
        q=json.loads(args.query.read_text())
        if q.get('attachments'): raise ValueError('expected a 3-computad')
        rules=[Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        m=Movies(Presentation(q['edges'],q['marks'],rules,q.get('mark_roots')),q['start'])
        h=tuple(map(tuple,q['source']))
        m.pres.walk(m.start,h,q.get('vertex'))
        answer=decide(m,h,q['first'],q['second'])
    else:
        answer=checks()
    print(json.dumps(answer))
