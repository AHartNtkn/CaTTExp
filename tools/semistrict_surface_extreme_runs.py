"""Factor runs at temporal extremes of the actual graph of polygon meetings."""
from argparse import ArgumentParser
from itertools import combinations,permutations,product
import json
from pathlib import Path

from semistrict_surface_signed_width_two import Movies,Presentation,Rule


def possible_joint_centers(arrows,moving):
    """Can one consistent choice of pair directions have two mixed moving vertices?"""
    possibilities={p:[((q,p),(p,r)) for q in arrows if p in arrows[q]
                      for r in arrows[p] if q!=r] for p in moving}
    for p,q in combinations(moving,2):
        for a in possibilities[p]:
            for b in possibilities[q]:
                if all((y,x) not in a for x,y in b):
                    return True
    return False


def three(calc,start,goal,initial,final,radius=None):
    from semistrict_surface_gain_runs import run
    from semistrict_surface_single_mover import solve
    before,after=calc.scan(start)[1],calc.scan(goal)[1]
    source_order=tuple(p for p,_ in start[0])
    target_order=tuple(p for p,_ in goal[0])
    unknown=False
    forward={}
    backward={}
    for tried,(first,p,last) in enumerate(permutations(source_order),1):
        if first not in forward:
            forward[first]=run(calc,start,source_order.index(first),after[first][0],final[first],radius)
        a,limited=forward[first]
        unknown|=limited
        if a is None:
            continue
        if last not in backward:
            backward[last]=run(calc,goal,target_order.index(last),before[last][0],initial[last],radius,
                               backwards=True)
        b,limited=backward[last]
        unknown|=limited
        if b is None:
            continue
        # Outside runs leave all other absolute cuts and the true total fixed.
        a_cuts={**initial,first:final[first]}
        b_cuts={**final,last:initial[last]}
        center=solve(calc,a,b,a_cuts,b_cuts,p,radius)
        if center['surface']:
            return dict(surface=True,endpoint_meetings=True,extreme_schedules=tried,
                        actions=[('run',first)]+center['actions']+[('run',last)])
        unknown|=center['surface'] is None
    return dict(surface=None if unknown else False,endpoint_meetings=None if unknown else False,
                extreme_schedules=tried,obstruction='no extreme-run schedule')


def checks():
    from random import Random
    from semistrict_surface_gain_runs import decide,run
    from semistrict_surface_packet_meetings import cut,transport
    from semistrict_surface_pair_runs import possible_gains
    from semistrict_surface_phase_gains import decide as phases,signature
    from semistrict_surface_polygon_cabling import rectangle
    from semistrict_surface_polygon_grades import resolution
    from semistrict_surface_raw_movie_graph import raw_compare,steps
    from semistrict_surface_shared_edge import braid_image
    from semistrict_surface_signed_meetings import Signed
    from semistrict_surface_single_polygon import expand
    from semistrict_surface_history_group import inv
    from semistrict_surface_single_power import output_order
    def sample(slot,path):
        s=((slot,'s'),)
        rule=Rule(path,s,((slot,'b'),(slot,'d')))
        m=Movies(Presentation({'f':(0,0)},{'s':('',''),'b':('','f'),'d':('f','')},
                             [rule],{'s':0,'b':0}),path)
        return m,s
    x=steps((1,0,1))+((0,0),(0,2),(0,4))+steps(rectangle(0,6,2))
    y=steps((0,1,0))+steps(rectangle(0,3,2))+((0,4),(0,3),(0,2))
    m,s=sample(0,'')
    yes=decide(m,s*5,x,y)
    assert yes['surface'] and yes['moving_triangle_centers']==[1] and not yes['endpoints_forced']
    assert not raw_compare(m,s*5,x,y)['raw'] and phases(m,s*5,x,y,True,True)['surface'] is None
    padded,t=sample(1,'f')
    no=decide(padded,t*5,x,y)
    assert no['surface'] is False and no['extreme_schedules']==6
    rng=Random(3309)
    graph_tests=0
    for n in (3,4,5):
        pairs=list(combinations(range(n),2))
        trials=product(range(4),repeat=3) if n==3 else (rng.choices(range(4),k=len(pairs)) for _ in range(160))
        for choices in trials:
            arrows={j:set() for j in range(n)}
            edges=[]
            for (p,q),v in zip(pairs,choices):
                oriented=[]
                if v&1:
                    arrows[p].add(q)
                    oriented.append((p,q))
                if v&2:
                    arrows[q].add(p)
                    oriented.append((q,p))
                if oriented: edges.append(oriented)
            moving=set(range(n)) if n==3 else {p for p in arrows if rng.randrange(4)}
            direct=any(len({p for p,_ in assignment}&{q for _,q in assignment}&moving)>=2
                       for assignment in product(*edges))
            assert possible_joint_centers(arrows,moving)==direct
            graph_tests+=1
    def letters(w):
        return tuple(('swap' if g>0 else 'inverse',abs(g)-1) for g in w)
    back_tests=back_yes=0
    for _ in range(650):
        n=rng.randrange(3,6)
        i=rng.randrange(n-1)
        w=tuple(rng.choice((-1,1))*rng.randrange(1,n) for _ in range(rng.randrange(2,12)))
        j=output_order(range(n),tuple(map(abs,w))).index(i)
        if j<=i: continue
        first=((0,i),)
        last=letters(w)+((0,j),)+letters(inv(expand(n,i,2,w)))
        def positive(v): return tuple(('swap' if p=='inverse' else p,k) for p,k in v)
        data=resolution(s*n,(positive(first),positive(last)),[(1,2)],'swap')
        calc=Signed(m,s*n,data)
        start,goal=[calc.decode(a,b) for a,b in zip((first,last),data[-1])]
        old=signature(calc,start)[1][0]
        result,limited=run(calc,goal,0,(),old,backwards=True)
        expected=transport(cut(braid_image(n,()),i,1),cut(braid_image(n,w),j,1))
        assert not limited and (result is not None)==expected
        if result is not None:
            assert signature(calc,result)==signature(calc,start)
        back_tests+=1
        back_yes+=expected
    full=exchanges=0
    for _ in range(90):
        n=5
        origins=rng.sample(range(n-1),3)
        first=tuple((0,i+sum(j<i for j in origins[:k])) for k,i in enumerate(origins))
        data=resolution(s*n,(first,first),[(1,2)],'swap')
        calc=Signed(m,s*n,data)
        start=movie=calc.decode(first,data[-1][0])
        oriented=set()
        moved=set()
        for step in range(9):
            opts=[]
            for k in range(2):
                other=calc.exchange(movie,k)
                if other is not None:
                    (p,i),(q,j)=movie[0][k:k+2]
                    opts.append((other,(p,q) if i<j else (q,p)))
            opts+=list(possible_gains(calc,movie,rng))
            if not opts: break
            movie,op=rng.choice(opts)
            if isinstance(op,tuple): oriented.add(op)
            else: moved.add(op)
        if len(moved)==3 and any(all(o.index(p)<o.index(q) for p,q in oriented)
                                 for o in permutations(moved)):
            ends=[signature(calc,z)[1] for z in (start,movie)]
            ans=three(calc,start,movie,*ends)
            assert ans['surface'] and ans['extreme_schedules']<=6
            full+=1
            exchanges+=bool(oriented)
    assert 0<back_yes<back_tests and exchanges and full
    return dict(transitive_example=yes,padded_negative=no,orientation_tests=graph_tests,
                backward_runs=back_tests,backward_positives=back_yes,three_mover_proofs=full,
                with_meetings=exchanges)


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
        source=tuple(map(tuple,q['source']))
        m.pres.walk(m.start,source,q.get('vertex'))
        answer=decide(m,source,q['first'],q['second'])
    else:
        answer=checks()
    print(json.dumps(answer))
