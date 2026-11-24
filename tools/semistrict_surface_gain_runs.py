"""Decide comparisons with no polygon meeting strictly inside a participant's gain run."""
from argparse import ArgumentParser
from collections import deque
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_component_braids import restrict
from semistrict_surface_history_group import inv
from semistrict_surface_packet_meetings import cut,transport
from semistrict_surface_phase_gains import executable_cut,signature
from semistrict_surface_polygon_grades import resolution
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_signed_meetings import Signed,follow,ordinary,orthogonal,verify_original
from semistrict_surface_signed_width_two import Movies,Presentation,Rule
from semistrict_surface_single_polygon import expand,transport_window
from semistrict_surface_single_power import output_order


def endpoints_forced(cuts,starts,ends):
    """Allow either spatial order, even when the actual braids may prevent a meeting."""
    packets={p:{e-1 for e in v.names} for p,v in cuts.items()}
    def interior(lo,hi,a,b):
        return (lo not in (a,b) or hi not in (a,b) or
                lo!=hi and len(b-a)>1)
    for a,b in combinations(packets,2):
        if packets[a]&packets[b]:
            continue
        for p,q in ((a,b),(b,a)):
            p0=starts[p]
            p1=(ends[p]&ends[q])-packets[q]
            q0=starts[q]|packets[p]|p0
            q1=ends[q]
            if p0<=p1 and q0<=q1:
                if interior(p0,p1,starts[p],ends[p]) or interior(q0,q1,starts[q],ends[q]):
                    return False
    return True


def run(calc,movie,k,goal_prefix,target_cut,radius=None):
    """Move just this occurrence to its specified absolute cut and replay the end."""
    boxes,seams=movie
    p,i=boxes[k]
    model=calc.model
    _,records,places,_=calc.scan(movie)
    h,_=places[p]
    prefix,_,_=records[p]
    rule=model.pres.rules[p]
    a,b=len(rule.source),len(rule.target)
    box='polygonWindow'
    _,off=model.named(h,p,i)
    root=h[:i]+((off,box),)+h[i+a:]
    pres=model.pres
    marks={**pres.marks,box:(rule.path,model.patch_ends[p])}
    vertex=pres.poles(rule.path)[0] if rule.path else pres.mark_roots[rule.source[0][1]]
    contracted=Movies(Presentation(pres.edges,marks,[],{**pres.mark_roots,box:vertex}),model.start)
    selected=[]
    offset=0
    for j,(_,e) in enumerate(h):
        if j<=i or j>=i+a:
            selected.append(offset)
        offset+=calc.flow[e]
    width=len(root)
    shadow=restrict(calc.width,inv(prefix)+goal_prefix,selected)
    j=output_order(range(width),tuple(map(abs,shadow))).index(i)
    if j<=i:
        return None,False
    path=executable_cut(contracted,root,shadow,j,1)
    if path is None:
        return None,False
    inputs=expand(width,i,a,path)
    outputs=expand(width,i,b,path)
    paths=seams[:k]+(seams[k]+inputs,inv(outputs)+seams[k+1])+seams[k+2:]
    result=boxes[:k]+((p,j),)+boxes[k+1:],paths
    _,r,_,_=calc.scan(result)
    w,slot,size=r[p]
    if cut(braid_image(calc.width,w),slot,size)!=target_cut:
        return None,False
    # If the representative itself is monotone its steps are the witness.
    at=i
    for g in map(abs,path):
        if g==at:
            break
        at+=g==at+1
    else:
        assert at==j
        return result,False
    # Give the private marked-window decision both positioned orthogonal
    # fractions. A successful monotone spelling can replace the gate word.
    upper,u=orthogonal(width,path)
    v,lower=orthogonal(width,path[::-1])
    final=follow(model,h,inputs)
    order=tuple(range(len(h)))
    final_order=output_order(order,tuple(map(abs,inputs)))
    answer=transport_window(model,p,(h,order,i),(final,final_order,j),
                            inv(lower[::-1])+v[::-1],upper+inv(u),radius)['surface']
    return (result if answer else None),answer is None


def decide(model,source,first,second,radius=None,certified_only=False):
    if model.attachments:
        raise ValueError('expected a positive 3-computad')
    if verify_original(model,source,first)!=verify_original(model,source,second):
        raise ValueError('expected parallel readings')
    arities=[(len(r.source),len(r.target)) for r in model.pres.rules]
    data=resolution(source,(ordinary(first),ordinary(second)),arities,'swap')
    def no(reason):
        return dict(endpoint_meetings=False,surface=False,obstruction=reason)
    if data is None:
        return no('named incidence')
    calc=Signed(model,source,data)
    start,goal=[calc.decode(w,r) for w,r in zip((first,second),data[-1])]
    h,initial,lower,total=signature(calc,start)
    end,final,upper,last=signature(calc,goal)
    if h!=end or total!=last:
        return no('resolved total or final names')
    if any(not lower[p]<=upper[p] or not transport(initial[p],final[p]) for p in initial):
        return no('unit packet transport')
    moving={p for p in initial if lower[p]!=upper[p]}
    if any(initial[p]!=final[p] for p in initial.keys()-moving):
        return no('stationary packet cut')
    forced=endpoints_forced(initial,lower,upper)
    if len(moving)==1:
        from semistrict_surface_single_mover import solve
        answer=solve(calc,start,goal,initial,final,next(iter(moving)),radius)
        return dict(answer,endpoint_meetings=answer['surface'],endpoints_forced=forced)
    from semistrict_surface_pair_runs import meeting_arrows,meeting_components,middle_polygons,solve as pair_runs
    if len(initial)==2:
        return dict(pair_runs(calc,start,goal,initial,final,moving,radius),endpoints_forced=forced)
    arrows=meeting_arrows(initial,final)
    components=meeting_components(arrows)
    independent=all(len(c)<=2 or len(c&moving)<=1 for c in components)
    middle=middle_polygons(arrows)&moving
    exact=forced or independent or not middle
    if certified_only and not exact:
        return dict(surface=None,moving_triangle_centers=sorted(middle))
    prefixes=calc.scan(goal)[1]
    finish=tuple(p for p,_ in goal[0]),frozenset(moving)
    source_key=tuple(p for p,_ in start[0]),frozenset()
    queue=deque([(source_key,start)])
    prev={source_key:None}
    unresolved=False
    while queue:
        state,movie=queue.popleft()
        order,done=state
        if state==finish:
            actions=[]
            while prev[state] is not None:
                state,action=prev[state]
                actions.append(action)
            return dict(surface=True,endpoint_meetings=True,endpoints_forced=forced,
                        moving_triangle_centers=sorted(middle),run_states=len(prev),actions=actions[::-1])
        def put(key,m,op):
            if m is not None:
                prev[key]=state,op
                queue.append((key,m))
        for k,p in enumerate(order):
            nxt=order,done|{p}
            if p in moving-done and nxt not in prev:
                candidate,unknown=run(calc,movie,k,prefixes[p][0],final[p],radius)
                unresolved|=unknown
                put(nxt,candidate,('run',p))
        for k,(p,q) in enumerate(zip(order,order[1:])):
            nxt=order[:k]+(q,p)+order[k+2:],done
            if nxt not in prev:
                put(nxt,calc.exchange(movie,k),('meet',p,q))
    if not exact and moving-middle:
        from semistrict_surface_phase_gains import decide as phases
        result=phases(model,source,first,second,split_signs=True,separate_runs=True,radius=radius)
        if result['surface'] is not None:
            return dict(result,endpoint_meetings=None if unresolved else False,
                        moving_triangle_centers=sorted(middle))
    return dict(surface=False if exact and not unresolved else None,
                endpoint_meetings=None if unresolved else False,endpoints_forced=forced,
                moving_triangle_centers=sorted(middle),independent_components=independent,run_states=len(prev))


def checks():
    from itertools import permutations,product
    from random import Random
    from semistrict_surface_phase_gains import decide as phases
    from semistrict_surface_link_schedules import decide as counts
    from semistrict_surface_polygon_cabling import rectangle
    from semistrict_surface_raw_movie_graph import raw_compare,steps
    from semistrict_surface_packet_meetings import Packet
    def literal(w):
        return tuple(('swap' if g>0 else 'inverse',abs(g)-1) for g in w)
    def splits(slot,path):
        s=((slot,'s'),)
        return Movies(Presentation({'f':(0,0)},{'s':('',''),'b':('','f'),'d':('f','')},
                      [Rule(path,s,((slot,'b'),(slot,'d'))),Rule('',((0,'s'),),((0,'s'),))],
                      {'s':0,'b':0}),path),s*3
    first=steps((1,0,1))+((0,0),(1,2))+steps(rectangle(0,2,2))
    last=steps((0,1,0))+((1,1),)+steps((0,1))+((0,2),)
    m,h=splits(0,'')
    yes=decide(m,h,first,last)
    assert yes['actions']==[('meet',0,1),('run',0)] and yes['endpoints_forced']
    assert counts(m,h,first,last)['surface'] is None and phases(m,h,first,last,True)['surface'] is None
    assert not raw_compare(m,h,first,last)['raw'] and m.compare(h,first,last)['surface']
    padded,h1=splits(1,'f')
    no=decide(padded,h1,first,last)
    assert no['surface'] is False and no['endpoints_forced']
    x=steps((1,0,1))+((0,0),)+steps(rectangle(0,2,1))+((0,0),)
    y=steps((0,1,0))+((0,1),)+steps(rectangle(0,1,2))+((0,2),)
    padded,h1=splits(0,'f')
    old=decide(padded,h1,x,y)
    assert old['surface'] is False and phases(padded,h1,x,y)['surface'] is None
    # The canonical representative moves the window left, although an
    # explicitly constructed signed spelling moves it monotonically right.
    w=(-2,1,-2,1,1)
    src=((0,0),)
    dst=literal(w)+((0,2),)+literal(inv(expand(3,0,2,w)))
    assert decide(m,h,src,dst)['surface']
    plain=Movies(Presentation({}, {'s':('','')},[],{'s':0}),'')
    u=executable_cut(plain,h,w,2,1)
    at=0
    for g in map(abs,u):
        if g==at: break
        at+=g==at+1
    else: raise AssertionError('expected a nonmonotone canonical path')
    # Independently enumerate temporal orders at a meeting and all possible
    # before-sets in the endpoint intervals, for pairs of packets on six units.
    rng=Random(2461)
    queries=locks=0
    for size_p,size_q in ((1,1),(1,2),(2,2)):
        n=6
        packets=(tuple(range(size_p)),tuple(range(size_p,size_p+size_q)))
        cuts={p:Packet((),tuple((i+1,) for i in v)) for p,v in enumerate(packets)}
        def records(order):
            return {p:frozenset(order[:order.index(v[0])]) for p,v in enumerate(packets)}
        meeting=[records(order) for order in permutations(range(n))
                 if all(order[order.index(v[0]):order.index(v[0])+len(v)]==v for v in packets)]
        def bounds():
            lo={}
            hi={}
            for p,packet in enumerate(packets):
                choices={e:rng.randrange(3) for e in range(n) if e not in packet}
                lo[p]=frozenset(e for e,k in choices.items() if k==0)
                hi[p]=frozenset(e for e,k in choices.items() if k!=2)
            return lo,hi
        for _ in range(300):
            lo,hi=bounds()
            brute=not any(all(lo[p]<=z[p]<=hi[p] for p in cuts) and
                          any(z[p] not in (lo[p],hi[p]) for p in cuts) for z in meeting)
            assert endpoints_forced(cuts,lo,hi)==brute
            queries+=1
            locks+=brute
    # Signed witnesses with arbitrary passive winding before and between
    # three or four successive gains on a spatially arity-changing polygon.
    signed=0
    for n in (4,5):
        for signs in product((1,-1),repeat=n-1):
            word=()
            for i,sign in enumerate(signs):
                exterior=tuple(rng.choice((-1,1))*rng.choice([k for k in range(1,n) if k not in (i,i+1)])
                               for _ in range(rng.randrange(4)))
                word+=exterior+(sign*(i+1),)
            dst=literal(word)+((0,n-1),)+literal(inv(expand(n,0,2,word)))
            assert decide(m,((0,'s'),)*n,src,dst)['surface']
            signed+=1
    # On one scalar gap contraction has an independent free-group
    # transport decision even for target braids with arbitrary backtracking.
    cases=positives=0
    for n in (3,4):
        for _ in range(250):
            w=tuple(rng.choice((-1,1))*rng.randrange(1,n) for _ in range(rng.randrange(10)))
            i=rng.randrange(n)
            j=output_order(range(n),tuple(map(abs,w))).index(i)
            a,b=cut(braid_image(n,()),i,1),cut(braid_image(n,w),j,1)
            dst=literal(w)+((0,j),)+literal(inv(expand(n,i,2,w)))
            expected=transport(a,b)
            assert decide(m,((0,'s'),)*n,((0,i),),dst)['surface']==expected
            positives+=expected
            cases+=1
    return dict(same_sign_splits=yes,padded_denial=no,response_250_padded=old,
                nonmonotone_gate=list(u),incidence_tests=queries,forced_pairs=locks,signed_runs=signed,
                scalar_contractions=cases,scalar_contractions_yes=positives)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    parser.add_argument('--radius',type=int,help='optional cap on the private transport search')
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        if q.get('attachments'): raise ValueError('expected a 3-computad')
        rules=[Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        model=Movies(Presentation(q['edges'],q['marks'],rules,q.get('mark_roots')),q['start'])
        source=tuple(map(tuple,q['source']))
        model.pres.walk(model.start,source,q.get('vertex'))
        ans=decide(model,source,q['first'],q['second'],args.radius)
    else:
        ans=checks()
    print(json.dumps(ans))
