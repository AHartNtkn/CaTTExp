"""Replay grouped runs outside the middle of a transitive triangle of potential meetings."""
from random import Random
import json

from semistrict_surface_gain_runs import decide,run
from semistrict_surface_packet_meetings import cut
from semistrict_surface_pair_runs import meeting_arrows,middle_polygons,possible_gains
from semistrict_surface_phase_gains import gain,signature
from semistrict_surface_polygon_grades import resolution
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_signed_meetings import Signed
from semistrict_surface_signed_width_two import Movies,Presentation,Rule


def regroup(calc,start,goal,actions):
    """Keep the meeting list fixed and group eligible gains in the promised gaps."""
    ends=[signature(calc,w)[1] for w in (start,goal)]
    arrows=meeting_arrows(*ends)
    obstructed=middle_polygons(arrows)
    moves={p for op,p,*_ in actions if op=='gain'}
    protected=moves-obstructed
    meetings=[(p,q) for op,p,q,*_ in actions if op=='meet']
    # p is temporally earlier than q; its gains can follow this meeting
    # and q's can precede it. Equal names never occur in opposite orientations.
    after={p:max((j+1 for j,(a,_) in enumerate(meetings) if a==p),default=0) for p in moves}
    before={p:min((j for j,(_,b) in enumerate(meetings) if b==p),default=len(meetings)) for p in moves}
    assert all(after[p]<=before[p] for p in protected)
    phases=[[] for _ in range(len(meetings)+1)]
    j=0
    for op,p,value in actions:
        if op=='meet':
            j+=1
        elif p not in protected:
            phases[j].append((p,value))
    final=calc.scan(goal)[1]
    for p in sorted(protected):
        phases[after[p]].append((p,None))
    movie=start
    for j,phase in enumerate(phases):
        for p,prefix in phase:
            order=[t for t,_ in movie[0]]
            if prefix is None:
                movie,unknown=run(calc,movie,order.index(p),final[p][0],ends[1][p])
                assert not unknown
            else:
                w,i,size=prefix
                movie=gain(calc,movie,order.index(p),cut(braid_image(calc.width,w),i,size),w)
            assert movie is not None
        if j<len(meetings):
            a,b=meetings[j]
            order=[t for t,_ in movie[0]]
            k=min(order.index(a),order.index(b))
            assert set(order[k:k+2])=={a,b}
            movie=calc.exchange(movie,k)
            assert movie is not None
    assert [p for p,_ in movie[0]]==[p for p,_ in goal[0]]
    assert signature(calc,movie)==signature(calc,goal)
    return len(protected),len(moves&obstructed),sum(after[p]>before[p] for p in moves)


def checks():
    from semistrict_surface_polygon_cabling import rectangle
    from semistrict_surface_raw_movie_graph import steps,raw_compare
    from semistrict_surface_phase_gains import decide as phases
    def sample(slot,path):
        s=((slot,'s'),)
        bubble=((slot,'b'),(slot,'d'))
        return Movies(Presentation({'f':(0,0)},{'s':('',''),'b':('','f'),'d':('f','')},
                      [Rule(path,s,bubble),Rule(path,bubble,s)],{'s':0,'b':0}),path),s
    x=steps((1,0,1))+((0,0),(0,2),(1,2))+steps(rectangle(2,1,2))+steps(rectangle(0,2,2))
    y=steps((0,1,0))+steps(rectangle(1,1,2))+((0,3),(1,3))+steps(rectangle(0,1,2))+((0,2),)
    m,s=sample(0,'')
    yes=decide(m,s*4,x,y)
    assert yes['surface'] and not yes['moving_triangle_centers'] and not yes['endpoints_forced']
    assert not raw_compare(m,s*4,x,y)['raw'] and phases(m,s*4,x,y,True)['surface'] is None
    assert m.compare(s*4,x,y)['surface']
    padded,t=sample(1,'f')
    no=decide(padded,t*4,x,y)
    assert no['surface'] is False and not no['independent_components'] and not no['endpoints_forced']
    # Actual signed movies. Keep every original meeting, including redundant
    # meetings; recompute all exterior approaches on the reorganized diagram.
    rng=Random(7447)
    grouped=other=bad=mixed=gains=swaps=bounded_examples=0
    for _ in range(160):
        n=rng.randrange(3,6)
        root=s*n
        origins=rng.sample(range(n),3)
        first=tuple((0,i+sum(j<i for j in origins[:k])) for k,i in enumerate(origins))
        data=resolution(root,(first,first),[(1,2),(2,1)],'swap')
        calc=Signed(m,root,data)
        start=movie=calc.decode(first,data[-1][0])
        actions=[]
        for _ in range(9):
            opts=[]
            for k in range(2):
                swapped=calc.exchange(movie,k)
                if swapped is not None:
                    (p,i),(q,j)=movie[0][k:k+2]
                    if i>j: p,q=q,p
                    opts.append((swapped,('meet',p,q)))
            for alt,p in possible_gains(calc,movie,rng):
                opts.append((alt,('gain',p,None)))
            if not opts: break
            movie,action=rng.choice(opts)
            if action[0]=='gain':
                p=action[1]
                action=('gain',p,calc.scan(movie)[1][p])
                gains+=1
            else:
                swaps+=1
            actions.append(action)
        a,b,c=regroup(calc,start,movie,actions)
        grouped+=a
        other+=b
        bad+=c
        mixed+=bool(a and b)
        if a and b and bounded_examples<12:
            first_cuts,last_cuts=(signature(calc,v)[1] for v in (start,movie))
            middle=middle_polygons(meeting_arrows(first_cuts,last_cuts))
            numbers={p:sum(op=='gain' and q==p for op,q,_ in actions) for p in first_cuts}
            if any(numbers[p]>1 for p in numbers.keys()-middle) and all(numbers[p]<=1 for p in middle):
                boxes,seams=movie
                target=[]
                for j,w in enumerate(seams):
                    target.extend(('swap' if g>0 else 'inverse',abs(g)-1) for g in w)
                    if j<len(boxes): target.append((0,boxes[j][1]))
                result=phases(m,root,first,target,split_signs=True,separate_runs=True)
                assert result['surface'] and any(op[0]=='run' for op in result['actions'])
                bounded_examples+=1
    assert grouped and other and mixed and bad and bounded_examples
    return dict(three_movers=yes,padded_negative=no,signed_proofs=160,literal_gains=gains,
                literal_meetings=swaps,grouped_polygons=grouped,middle_polygons=other,
                mixed_proofs=mixed,actual_out_of_order_roles=bad,mixed_phase_decisions=bounded_examples)


if __name__=='__main__':
    print(json.dumps(checks()))
