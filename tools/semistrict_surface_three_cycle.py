"""Decide cyclic three-polygon comparisons when the required intermediate packets fill their gaps."""
from argparse import ArgumentParser
from itertools import groupby,permutations,product
import json
from pathlib import Path

from semistrict_surface_component_braids import restrict
from semistrict_surface_history_group import inv
from semistrict_surface_packet_meetings import cut,gain_factors
from semistrict_surface_phase_gains import first_slot_braid,intermediate,slots,substitute
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_meridian_transport import content,prod
from semistrict_surface_pair_runs import precedes
from semistrict_surface_signed_meetings import passive_meeting
from semistrict_surface_signed_width_two import Movies,Presentation,Rule


def gap_checkpoints(n,source,goal):
    """All possible projected cuts if at most one retained unit is gained per sign."""
    w,i,k=source
    z,j,_=goal
    old=cut(braid_image(n,w),i,k)
    new=cut(braid_image(n,z),j,k)
    if j<i or j==i and old!=new:
        return []
    candidates=[(w,i),(z,j)]
    if j-i<=1:
        return candidates
    factors=gain_factors(old,new)
    if factors is None:
        return []
    neg,pos=factors
    if j-i>2 or not neg or not pos:
        return None
    for negative,v in ((True,neg),(False,prod(neg,pos,inv(neg)))):
        target=intermediate(old,v,negative)
        local=substitute(braid_image(n,inv(w)),v)
        edge=i+k
        atom=prod(tuple((abs(x)-edge)*(1 if x>0 else -1) for x in local if abs(x)>edge))
        exposure=first_slot_braid(n-edge,atom)
        if exposure is None: continue
        sign=-1 if negative else 1
        prefix=w+slots(exposure,edge)+tuple(sign*g for g in range(edge,i,-1))
        if cut(braid_image(n,prefix),i+1,k)==target:
            candidates.append((prefix,i+1))
    return candidates


def bracket(calc,p,q,r,old,new,first,last):
    """Compute the intermediate outer cuts between initial q and final r."""
    lo,hi=old[q].after,new[r].before
    left,right=first[q],last[r]
    if not precedes(old[q],new[r]):
        return False
    gap=content(hi).keys()-content(lo).keys()
    names=set(old[p].names)
    if not names<=gap:
        return False
    # The interpolating before-set includes the whole earlier through-cut
    # and excludes the later packet and its entire suffix.
    mandatory=content(old[p].before).keys()|content(lo).keys()
    possible=content(new[p].before).keys() & (content(hi).keys()-names)
    if not mandatory<=possible:
        return False
    w,i,k=left
    z,j,l=right
    assert i+k+len(gap)==j
    legs=passive_meeting(calc.width,inv(w)+z,(i,k),(j,l))
    assert legs is not None
    anchor=w+legs[0]
    selected={e-1 for e in gap}
    base=restrict(calc.width,anchor,selected)
    def projection(prefix,t):
        return restrict(calc.width,prefix,selected),len(content(t.before).keys() & gap),len(names)
    points=gap_checkpoints(len(gap),projection(first[p][0],old[p]),projection(last[p][0],new[p]))
    if points is None: return None
    if not points: return False
    candidates={}
    for projected,location in points:
        word=anchor+slots(inv(base)+projected,i+k)
        target=cut(braid_image(calc.width,word),i+k+location,len(names))
        assert target.names==old[p].names
        candidates[target]=word
    return tuple((w,t) for t,w in candidates.items())


def chronological(order,meetings,goal):
    order=list(order)
    for p,q in meetings:
        i,j=order.index(p),order.index(q)
        if abs(i-j)!=1:
            return False
        order[i],order[j]=order[j],order[i]
    return tuple(order)==goal


def cycle(calc,start,goal,old,new,radius=None):
    from semistrict_surface_gain_runs import run
    order=tuple(p for p,_ in start[0])
    target=tuple(p for p,_ in goal[0])
    first,last=(calc.scan(m)[1] for m in (start,goal))
    tried=unresolved=discarded=0
    for a,b,c in permutations(order):
        orientations=((a,b),(c,a),(b,c))
        if not all(precedes(old[p],new[q]) for p,q in orientations):
            continue
        for fourth in (False,True):
            meetings=orientations+(((a,b),) if fourth else ())
            if not chronological(order,meetings,target):
                continue
            fixed={b:bracket(calc,b,a,c,old,new,first,last)}
            if fourth: fixed[a]=bracket(calc,a,c,b,old,new,first,last)
            if any(x is False for x in fixed.values()):
                discarded+=1
                continue
            if any(x is None for x in fixed.values()):
                unresolved+=1
                continue
            instructions=[('part',b),('meet',a,b),('part' if fourth else 'run',a),
                          ('meet',c,a),('run',c),('meet',b,c),('run',b)]
            if fourth: instructions += [('meet',a,b),('run',a)]
            for choices in product(*fixed.values()):
                tried+=1
                checkpoints=dict(zip(fixed,choices))
                movie=start
                for step in instructions:
                    op,p,*rest=step
                    boxes=movie[0]
                    indices={t:k for k,(t,_) in enumerate(boxes)}
                    k=indices[p]
                    if op=='meet':
                        q,=rest
                        if boxes[k][1]>=boxes[indices[q]][1]:
                            break
                        movie=calc.exchange(movie,min(k,indices[q]))
                    else:
                        prefix,t=checkpoints[p] if op=='part' else (last[p][0],new[p])
                        movie,limited=run(calc,movie,k,prefix,t,radius)
                        if limited: unresolved+=1
                    if movie is None: break
                else:
                    return dict(surface=True,cycle_schedules=tried,cycle_blocks=len(meetings),
                                actions=instructions)
    return dict(surface=None if unresolved else False,cycle_schedules=tried,
                open_cycle_schedules=unresolved,excluded_brackets=discarded)


def solve(calc,start,goal,old,new,radius=None):
    from semistrict_surface_extreme_runs import three
    extremes=three(calc,start,goal,old,new,radius)
    if extremes['surface']:
        return extremes
    result=cycle(calc,start,goal,old,new,radius)
    if extremes['surface'] is None and result['surface'] is False:
        result['surface']=None
    return dict(result,extreme_schedules=extremes['extreme_schedules'])


def checks():
    from semistrict_surface_component_braids import cabling
    from semistrict_surface_extreme_runs import three
    from semistrict_surface_gain_runs import decide
    from semistrict_surface_phase_gains import signature
    from semistrict_surface_polygon_grades import resolution
    from semistrict_surface_raw_movie_graph import raw_compare,steps
    from semistrict_surface_signed_meetings import Signed,ordinary,verify_original
    from semistrict_surface_single_power import output_order
    def letters(w):
        return tuple(('swap' if g>0 else 'inverse',abs(g)-1) for g in w)
    def prepare(model,h,x,y):
        assert verify_original(model,h,x)==verify_original(model,h,y)
        data=resolution(h,(ordinary(x),ordinary(y)),
                        [(len(r.source),len(r.target)) for r in model.pres.rules],'swap')
        calc=Signed(model,h,data)
        a,b=[calc.decode(w,t) for w,t in zip((x,y),data[-1])]
        ends=[signature(calc,z)[1] for z in (a,b)]
        return calc,a,b,*ends
    # Three independent birth/death splits, cabled from named macro readings.
    def old(stages):
        names=['B','A','C']
        sizes=dict.fromkeys(names,1)
        out=()
        for w,p in stages:
            k=0
            face=[]
            for e in names:
                face.append((e,k,k+sizes[e]))
                k+=sizes[e]
            out+=letters(cabling(face,w))
            names=output_order(names,tuple(map(abs,w)))
            if p is not None:
                out+=((0,sum(sizes[e] for e in names[:names.index(p)])),)
                sizes[p]=2
        return out
    x=steps((1,0,1))*3+old([((1,),'A'),((1,),'B'),((2,1),'C')])
    y=steps((0,1,0))*3+old([((),'C'),((2,1),'A'),((2,),'B'),((2,),None)])
    def splits(k,path):
        s=((k,'s'),)
        return Movies(Presentation({'f':(0,0)},{'s':('',''),'b':('','f'),'d':('f','')},
                     [Rule(path,s,((k,'b'),(k,'d')))],{'s':0,'b':0}),path),s*3
    m,h=splits(0,'')
    yes=cycle(*prepare(m,h,x,y))
    assert yes['surface'] and yes['cycle_blocks']==4 and not raw_compare(m,h,x,y)['raw']
    m,h=splits(1,'f')
    no=solve(*prepare(m,h,x,y))
    assert no['surface'] is False and not no['open_cycle_schedules']
    # Moving single scalars between the two ends of a fixed spatial edge
    # controls the two signed approaches independently of the named braid.
    both=three_yes=essential=0
    for u,v,d,e in product((1,-1),repeat=4):
        site=lambda z:int(z<0)
        ports=[(site(-u),site(d)),(site(e),site(-v)),(site(u),site(v))]
        rules=[Rule('f',((a,'s'),),((b,'s'),)) for a,b in ports]
        m=Movies(Presentation({'f':(0,0)},{'s':('','')},rules,{'s':0}),'f')
        h=tuple((a,'s') for a,_ in ports)
        x=((0,0),)+letters((-d,))+((1,0),)+letters((d,2*v,u))+((2,0),)
        y=((2,2),)+letters((2*v,u,2*e))+((0,2),)+letters((-2*e,))+((1,2),)
        result=cycle(*prepare(m,h,x,y))
        assert result['surface'] and result['cycle_blocks']==4
        both+=1
        if (u,v,d,e)==(1,1,1,1):
            bounded=decide(m,h,x,y,only_endpoint_meetings=True)
            assert bounded['endpoint_meetings'] is False
            assert three(*prepare(m,h,x,y))['surface'] is False
            assert decide(m,h,x,y)['surface']
            indispensable=result
            essential+=1
        # The three-block direction ends with A already at the middle slot.
        z=((2,2),)+letters((2*v,u))+((1,2),(0,1))
        try:
            compatible=verify_original(m,h,z)==verify_original(m,h,x)
        except ValueError:
            compatible=False
        if compatible:
            triple=cycle(*prepare(m,h,x,z))
            assert triple['surface'] and triple['cycle_blocks']==3
            three_yes+=1
    # Known four- and five-strand gap cut paths embedded between two
    # external packet anchors. Change each anchor independently by a
    # passive braid before computing their common full frame.
    from types import SimpleNamespace
    from random import Random
    rng=Random(8827)
    interpolations=twice=0
    for n in (5,6,7):
        for _ in range(40):
            anchor=tuple(rng.choice((-1,1))*rng.randrange(1,n) for _ in range(4))
            left=anchor+(2,3,2)
            right=anchor+(-1,-2,-1)
            oldp=anchor+(1,)
            first_cross=2*rng.choice((-1,1))
            opposite=rng.choice((True,False))
            crossings=(first_cross,-3 if first_cross>0 else 3) if opposite else (first_cross,)
            past=anchor+crossings
            loc=1+len(crossings)
            # Bring the right anchor to the mover, skipping the untouched
            # spectators, then gain it. This step disappears in the gap.
            endp=past+tuple(range(n-1,loc,-1))
            first={0:(left,0,1),1:(oldp,0,1)}
            last={1:(endp,loc+1,1),2:(right,n-1,1)}
            def cuts(d):
                return {p:cut(braid_image(n,w),i,k) for p,(w,i,k) in d.items()}
            candidates=bracket(SimpleNamespace(width=n),1,0,2,cuts(first),cuts(last),first,last)
            targets={t for _,t in candidates}
            for j in range(len(crossings)+1):
                assert cut(braid_image(n,anchor+crossings[:j]),1+j,1) in targets
            twice+=opposite
            interpolations+=1
    def subseq(w,s):
        it=iter(w)
        return all(v in it for v in s)
    cases=allowed=0
    for length in range(3,10):
        for w in product(range(3),repeat=length):
            if len(set(w))!=3: continue
            temporal=not any(subseq(w,(g,(g+1)%3,(g+2)%3)) for g in range(3))
            reduced=tuple(g for g,_ in groupby(w))
            a=w[0]
            pattern=(a,(a+2)%3,(a+1)%3)
            assert temporal==(reduced in (pattern,pattern+(a,)))
            cases+=1
            allowed+=temporal
    assert three_yes and essential
    return dict(old_four_block_surface_only=yes,padded_negative=no,signed_four_blocks=both,
                signed_three_blocks=three_yes,indispensable_split_run=indispensable,
                temporal_words=cases,allowed_words=allowed,anchored_gaps=interpolations,
                gaps_with_two_opposite_gains=twice)


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
