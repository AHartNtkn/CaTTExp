"""Decide signed polygon schedules when their two cohort prefix ranges are finite."""
from heapq import heappop, heappush
from itertools import count, product

from semistrict_surface_cohort_orbits import cohort_chart
from semistrict_surface_component_braids import restrict
from semistrict_surface_gap_orbits import expose, slide
from semistrict_surface_gain_runs import run
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_meridian_transport import content
from semistrict_surface_packet_meetings import cut, transport
from semistrict_surface_phase_gains import slots
from semistrict_surface_prefix_values import prefix_values, separated_sites
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_single_power import output_order


def positioned_points(calc,owner,data,mandatory,allowed):
    width,source,goal,anchor,offset,gap_width = data
    sorted_data = cohort_chart(source,goal,anchor,offset,gap_width)
    if sorted_data is False:
        return ()
    chart,split,count = sorted_data
    _,slot,size = source
    begin = offset+slot+size
    order = output_order(range(width),tuple(map(abs,chart)))
    def projections(start,length):
        if length<=1:
            return [((),k) for k in range(length+1)]
        names = frozenset(order[start:start+length])
        readings = separated_sites(calc,names)
        if readings is None:
            values = prefix_values(calc,owner,names,mandatory,allowed)
            if values is None:
                return None
            readings = values.values()
        base = restrict(width,chart,names)
        return [(reduced(inv(base)+path),k) for path,k in readings]
    negative,positive = projections(begin,split),projections(begin+split,count-split)
    if negative==[] or positive==[]:
        return ()
    if negative is None or positive is None:
        return None
    points = {}
    for (left,a),(right,c) in product(negative,positive):
        # In the sorted chart the already-gained subblocks have lengths a,c.
        # Bring the c positives ahead of the as-yet unpassed negatives.
        selected_neg = tuple(range(a))+tuple(range(a+c,split+c))
        sorting = tuple(-g for g in expose(selected_neg,count))
        before = slots(left,begin)+slots(right,begin+split)+slots(inv(sorting),begin)
        word = reduced(chart+before+slots(slide(size,a,-1),offset+slot)+slots(slide(size,c,1),offset+slot+a))
        point = cut(braid_image(width,word),offset+slot+a+c,size)
        points[point] = word
    return tuple((w,t) for t,w in points.items())


def before(packet):
    return frozenset(x-1 for x in content(packet.before))


def finite_search(calc,start,goal,old,new,grouped=(),radius=None):
    first,last = (calc.scan(m)[1] for m in (start,goal))
    points = []
    for p in range(len(old)):
        entries = {old[p]:first[p][0],new[p]:last[p][0]}
        if old[p]!=new[p] and p not in grouped:
            data = calc.width,first[p],last[p],(),0,calc.width
            options = positioned_points(calc,p,data,before(old[p]),before(new[p]))
            if options is None:
                return dict(surface=None,infinite_prefix_at=p)
            for word,t in options:
                if before(old[p])<=before(t)<=before(new[p]) and transport(old[p],t) and transport(t,new[p]):
                    entries[t] = word
        points.append(tuple(entries.items()))
    initial = tuple(p for p,_ in start[0]),(0,)*len(points)
    final = tuple(p for p,_ in goal[0]),tuple(next(i for i,(t,_) in enumerate(row) if t==new[p])
                                              for p,row in enumerate(points))
    queue = []
    seen = set()
    ticket = count()
    final_order = {p:i for i,p in enumerate(final[0])}

    def enqueue(state,movie):
        if movie is None or state in seen:
            return
        order,at = state
        remaining = sum(a!=b for a,b in zip(at,final[1]))
        inversions = sum(final_order[p]>final_order[q] for i,p in enumerate(order) for q in order[i+1:])
        heappush(queue,(remaining+inversions,next(ticket),state,movie))
        seen.add(state)

    enqueue(initial,start)
    unresolved = False
    while queue:
        _,_,state,movie = heappop(queue)
        order,at = state
        if state==final:
            return dict(surface=True,finite_cut_states=len(seen))
        for k,p in enumerate(order):
            for i,(target,word) in enumerate(points[p]):
                key = order,at[:p]+(i,)+at[p+1:]
                if key in seen or not before(points[p][at[p]][0])<before(target):
                    continue
                nxt,limited = run(calc,movie,k,word,target,radius)
                unresolved |= limited
                enqueue(key,nxt)
        for k in range(len(order)-1):
            key = order[:k]+(order[k+1],order[k])+order[k+2:],at
            if key not in seen:
                enqueue(key,calc.exchange(movie,k))
    return dict(surface=None if unresolved else False,finite_cut_states=len(seen))


def prepared(model,root,x,y):
    from semistrict_surface_polygon_grades import resolution
    from semistrict_surface_signed_meetings import Signed,ordinary,verify_original
    from semistrict_surface_phase_gains import signature
    assert verify_original(model,root,x)==verify_original(model,root,y)
    arities = [(len(r.source),len(r.target)) for r in model.pres.rules]
    data = resolution(root,(ordinary(x),ordinary(y)),arities,'swap')
    calc = Signed(model,root,data)
    a,b = [calc.decode(w,t) for w,t in zip((x,y),data[-1])]
    old,new = [signature(calc,m)[1] for m in (a,b)]
    return calc,a,b,old,new


def checks():
    from semistrict_surface_gap_orbits import positive_example,endpoint_symmetries
    from semistrict_surface_polygon_cabling import rectangle
    from semistrict_surface_signed_width_two import Movies,Presentation,Rule
    from semistrict_surface_three_cycle import bracket,cycle,solve
    *_,x,y,_ = positive_example(0,None)
    edges,marks,roots = {'f':(0,0)},{'s':('','')},{'s':0}
    for n in (2,3):
        root = ((n,'s'),)*3+tuple((i,'s') for i in range(n))
        exterior = tuple(('swap',i) for i in rectangle(0,3,n))
        for padded in (False,True):
            width = n if padded else 0
            s = ((width,'s'),)
            model = Movies(Presentation(edges,marks,[Rule('f'*width,s,s)]*3,roots),'f'*n)
            args = prepared(model,root,x+exterior,exterior+tuple((r,i+n) for r,i in y))
            calc,a,b,old,new = args
            end,first,_,total = calc.scan(a)
            f = bracket(calc,1,0,2,old,new,first,calc.scan(b)[1])
            assert not any(endpoint_symmetries(calc,q,end,total,(*old.values(),*new.values()))
                           for q in (f.forward,f.backward,f.cohorts))
            choices = positioned_points(calc,1,f.chart_data,before(old[1]),before(new[1]))
            assert len(choices)==2**n
            answer = cycle(*args)
            assert answer['surface'] != padded and answer['surface'] is not None
            if padded:
                assert answer['open_cycle_schedules']==0
            assert solve(*args)['surface']==(not padded)
    m = 4
    root = tuple((i+2,'s') for i in range(m))+((0,'s'),(1,'s'))
    exterior = tuple(('swap',i) for i in rectangle(0,m,2))
    x = tuple((i,i) for i in range(m))+exterior
    y = exterior+tuple((i,i+2) for i in reversed(range(m)))
    for padded in (False,True):
        rules = []
        for i in range(m):
            width = i+2 if i==1 and padded else 0
            s = ((width,'s'),)
            rules.append(Rule('f'*width,s,s))
        model = Movies(Presentation(edges,marks,rules,roots),'f'*(m+1))
        result = finite_search(*prepared(model,root,x,y))
        assert result['surface']==(not padded)
    print('All three endpoint symmetry tests fail on four positive three-polygon inputs; '
          'positioned cuts decide those and two four-polygon inputs')


if __name__=='__main__':
    checks()
