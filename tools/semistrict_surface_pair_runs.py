"""Decide arbitrary two-polygon comparisons, testing at most two directed schedules."""
from argparse import ArgumentParser
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_history_group import inv
from semistrict_surface_meridian_transport import content,prod,quasi
from semistrict_surface_signed_width_two import Movies,Presentation,Rule


def precedes(source,target):
    """The initial left through-cut and final right before-cut share a frame in this order."""
    return quasi(prod(inv(source.after),target.before))


def meeting_components(initial,final):
    graph={p:set() for p in initial}
    for p,q in combinations(graph,2):
        if precedes(initial[p],final[q]) or precedes(initial[q],final[p]):
            graph[p].add(q)
            graph[q].add(p)
    parts=[]
    unseen=set(graph)
    while unseen:
        root=min(unseen)
        part={root}
        todo=[root]
        while todo:
            v=todo.pop()
            for q in graph[v]-part:
                part.add(q)
                todo.append(q)
        unseen-=part
        parts.append(part)
    return parts


def solve(calc,start,goal,initial,final,moving,radius=None):
    from semistrict_surface_gain_runs import run
    order=tuple(p for p,_ in start[0])
    dest=tuple(p for p,_ in goal[0])
    p,q=order
    records=calc.scan(goal)[1]
    if order==dest:
        # Repeated meetings can be brought together and cancelled.
        schedules=[(('run',p),('run',q))]
    else:
        schedules=[(('run',right),('meet',left),('run',left))
                   for left,right in ((p,q),(q,p)) if precedes(initial[left],final[right])]
    unknown=False
    for tried,schedule in enumerate(schedules,1):
        movie=start
        actions=[]
        for op,v in schedule:
            if op=='meet':
                result=calc.exchange(movie,0)
                actions.append((op,*order))
            elif v in moving:
                k=next(k for k,(t,_) in enumerate(movie[0]) if t==v)
                result,bounded=run(calc,movie,k,records[v][0],final[v],radius)
                unknown|=bounded
                actions.append((op,v))
            else:
                continue
            if result is None:
                break
            movie=result
        else:
            return dict(surface=True,endpoint_meetings=True,pair_schedules=tried,actions=actions)
    answer=None if unknown else False
    return dict(surface=answer,endpoint_meetings=answer,pair_schedules=len(schedules),
                obstruction='no oriented two-polygon schedule')


def checks():
    from random import Random
    from semistrict_surface_polygon_grades import resolution
    from semistrict_surface_polygon_cabling import rectangle
    from semistrict_surface_raw_movie_graph import steps,raw_compare
    from semistrict_surface_phase_gains import decide as phases
    from semistrict_surface_gain_runs import decide
    from semistrict_surface_signed_meetings import Signed,follow
    from semistrict_surface_order_locks import permits
    from semistrict_surface_packet_meetings import cut
    from semistrict_surface_shared_edge import braid_image
    def sample(slot,path):
        s=((slot,'s'),)
        rule=Rule(path,s,((slot,'b'),(slot,'d')))
        m=Movies(Presentation({'f':(0,0)},{'s':('',''),'b':('','f'),'d':('f','')},
                             [rule],{'s':0,'b':0}),path)
        return m,s
    x=steps((1,0,1))+((0,0),(0,2))+steps(rectangle(2,2,2))+steps(rectangle(0,2,2))
    y=steps((0,1,0))+steps(rectangle(1,1,2))+((0,3),)+steps(rectangle(0,1,2))+((0,2),)
    m,s=sample(0,'')
    yes=decide(m,s*4,x,y)
    assert yes['actions']==[('run',1),('meet',0,1),('run',0)]
    assert not yes['endpoints_forced'] and phases(m,s*4,x,y,True)['surface'] is None
    assert not raw_compare(m,s*4,x,y)['raw']
    padded,t=sample(1,'f')
    no=decide(padded,t*4,x,y)
    assert no['surface'] is False and not no['endpoints_forced']
    # Compare the ordinary positive-interval test with the free-group
    # prefix-product condition on pairs of signed cuts in one positive braid.
    rng=Random(3322)
    queries=allowed=0
    for _ in range(550):
        n=rng.randrange(3,7)
        w=tuple(rng.randrange(1,n) for _ in range(rng.randrange(2,13)))
        a,b=rng.randrange(len(w)+1),rng.randrange(len(w)+1)
        def at(k):
            f=braid_image(n,w[:k])
            i=rng.randrange(n)
            size=rng.randint(1,min(3,n-i))
            row=cut(f,i,size)
            return row,(frozenset(e-1 for e in content(row.before)),
                        tuple(e-1 for e in row.names),k)
        ca,pa=at(a)
        cb,pb=at(b)
        actual=precedes(ca,cb)
        assert permits((n,w,w,{0:pa},{1:pb}),0,1)==actual
        queries+=1
        allowed+=actual
    # Build independent signed proofs from literal native gains and signed
    # meetings. The two actual birth/death windows have changing arities.
    def write(movie):
        boxes,seams=movie
        out=[]
        for j,w in enumerate(seams):
            out.extend(('swap' if g>0 else 'inverse',abs(g)-1) for g in w)
            if j<len(boxes):
                out.append((0,boxes[j][1]))
        return tuple(out)
    proofs=both=round_trips=native=meetings=0
    for _ in range(160):
        n=rng.randrange(3,6)
        root=s*n
        i,j=rng.sample(range(n),2)
        first=((0,i),(0,j+(j>i)))
        data=resolution(root,(first,first),[(1,2)],'swap')
        calc=Signed(m,root,data)
        movie=calc.decode(first,data[-1][0])
        gained=set()
        old_meets=0
        for step in range(8):
            boxes,seams=movie
            opts=[]
            swapped=calc.exchange(movie,0)
            if swapped is not None:
                opts.append((swapped,None))
            places=calc.scan(movie)[2]
            for k,(p,i) in enumerate(boxes):
                h,_=places[p]
                if i+1==len(h): continue
                # Choose an exterior approach on the current right side.
                u=()
                for _ in range(rng.randrange(3)):
                    options=[g for j in range(i+2,len(h)) for g in (j,-j)
                             if calc.model.swap(h,abs(g)-1,g>0) is not None]
                    if not options: break
                    g=rng.choice(options)
                    h=follow(calc.model,h,(g,))
                    u+=(g,)
                off=calc.model.named(h,p,i)[1]
                for cross in calc.model.prism_words(h,p,i,off):
                    sign=1 if cross[0]>0 else -1
                    out=tuple(g+(1 if g>0 else -1) for g in u)
                    dual=(sign*(i+2),sign*(i+1))
                    paths=seams[:k]+(seams[k]+u+cross,inv(dual)+inv(out)+seams[k+1])+seams[k+2:]
                    opts.append(((boxes[:k]+((p,i+1),)+boxes[k+1:],paths),p))
            if not opts: break
            movie,act=rng.choice(opts)
            if act is None: old_meets+=1
            else:
                native+=1
                gained.add(act)
        answer=decide(m,root,first,write(movie))
        assert answer['surface'] is True
        if len(gained)==2:
            both+=1
            assert answer['pair_schedules']<=2
            if old_meets>=2 and old_meets%2==0:
                round_trips+=1
                assert all(op[0]!='meet' for op in answer['actions'])
        meetings+=old_meets
        proofs+=1
    assert both and round_trips
    return dict(two_splits=yes,padded_negative=no,corner_tests=queries,corner_meetings=allowed,
                signed_proofs=proofs,both_moving=both,even_return_schedules=round_trips,
                observed_native_gains=native,observed_meetings=meetings)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    args=parser.parse_args()
    if args.query:
        from semistrict_surface_gain_runs import decide
        q=json.loads(args.query.read_text())
        if q.get('attachments'): raise ValueError('expected a 3-computad')
        rules=[Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        model=Movies(Presentation(q['edges'],q['marks'],rules,q.get('mark_roots')),q['start'])
        h=tuple(map(tuple,q['source']))
        model.pres.walk(model.start,h,q.get('vertex'))
        answer=decide(model,h,q['first'],q['second'])
    else:
        answer=checks()
    print(json.dumps(answer))
