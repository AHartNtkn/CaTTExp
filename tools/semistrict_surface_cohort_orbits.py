"""Compute the pure spectator symmetries left after prescribing both packet cuts."""
from collections import deque
from functools import lru_cache
from itertools import combinations

from semistrict_surface_gap_orbits import Orbit, expose, pure_generators, slide
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_meridian_transport import content, prod, quasi
from semistrict_surface_packet_meetings import cut, gain_factors
from semistrict_surface_phase_gains import slots, substitute
from semistrict_surface_component_braids import restrict
from semistrict_surface_shared_edge import braid_image


@lru_cache(maxsize=512)
def sorted_frame(n, negative, positive, shadow):
    """Find a suffix braid with the specified two prefix products."""
    total = prod(negative,positive)
    all_names = tuple(range(1,n+1))
    rest = prod(inv(total),all_names)
    if not all(quasi(x) for x in (negative,positive,rest)):
        return None
    groups = [content(x) for x in (negative,positive,rest)]
    if any(v!=1 for group in groups for v in group.values()):
        return None
    a,b = len(groups[0]),len(groups[0])+len(groups[1])
    targets = negative,total
    standard = all_names[:a],all_names[:b]
    # Try the suffix order appearing in the given terminal reading first.
    for initial in ((),shadow):
        frame = braid_image(n,initial)
        order = [i for group in groups for i in range(n) if cut(frame,i,1).names[0] in group]
        sort = expose(order,n)
        for tail in ((),sort,tuple(-g for g in sort)):
            path = initial+tail
            frame = braid_image(n,path)
            if (prod(*frame[:a]),prod(*frame[:b]))==targets:
                return path
    # Quasipositive decompositions concatenate to a full Artin frame, so
    # the two based prefix products have already passed the orbit test.
    actions = [(g,braid_image(n,(g,))) for k in range(1,n) for g in (k,-k)]
    todo,seen = deque([(targets,())]),{targets}
    while todo:
        values,path = todo.popleft()
        for g,frame in actions:
            nxt = tuple(substitute(frame,v) for v in values)
            if nxt==standard:
                return path+(-g,)
            if nxt not in seen:
                seen.add(nxt)
                todo.append((nxt,path+(-g,)))
    raise AssertionError('Realizable pair of prefix products has no Artin frame')


def cohort_chart(source,goal,anchor,offset,gap_width):
    w,i,size = source
    z,j,_ = goal
    old,new = cut(braid_image(gap_width,w),i,size),cut(braid_image(gap_width,z),j,size)
    factors = gain_factors(old,new)
    if factors is None:
        return False
    basis = braid_image(gap_width,inv(w))
    begin = i+size
    local = [substitute(basis,x) for x in factors]
    if any(abs(g)<=begin for word in local for g in word):
        return False
    negative,positive = (slots(word,-begin) for word in local)
    n = gap_width-begin
    shadow = restrict(gap_width,inv(w)+z,set(range(begin,gap_width)))
    match = sorted_frame(n,negative,positive,shadow)
    if match is None:
        return False
    split = len(content(negative))
    count = split+len(content(positive))
    assert count==j-i
    chart = reduced(anchor+slots(w,offset)+slots(match,offset+begin))
    return chart,split,count


def cohort_orbit(width,source,goal,anchor,offset,gap_width):
    data = cohort_chart(source,goal,anchor,offset,gap_width)
    if data is False:
        return False
    chart,split,count = data
    _,i,size = source
    begin = i+size
    generators = tuple(reduced(chart+slots(g,offset+begin+base)+inv(chart))
                       for base,length in ((0,split),(split,count-split)) for g in pure_generators(length))
    points = {}
    # The checkpoint depends on two prefix products in the sorted chart.
    # Use a representative with the selected negatives and positives first.
    for length in range(count+1):
        for chosen in combinations(range(count),length):
            chosen = set(chosen)
            neg = tuple(t for t in range(split) if t in chosen)
            pos = tuple(t for t in range(split,count) if t in chosen)
            other_neg = tuple(t for t in range(split) if t not in chosen)
            other_pos = tuple(t for t in range(split,count) if t not in chosen)
            internal = expose(neg+other_neg+pos+other_pos,count)
            order = neg+pos+other_neg+other_pos
            sorting = tuple(-g for g in expose([k for k,t in enumerate(order) if t<split],count))
            before = internal+inv(sorting)
            word = reduced(chart+slots(before,offset+begin))
            for k,t in enumerate(neg+pos):
                word += slots(slide(size,1,-1 if t<split else 1),offset+i+k)
            point = cut(braid_image(width,word),offset+i+length,size)
            points[point] = word
    return Orbit(tuple((w,t) for t,w in points.items()),generators)


def validate_paths():
    from random import Random
    from semistrict_surface_single_power import output_order
    rng = Random(497)
    total = mixed = twists = 0
    for _ in range(110):
        size,left,right = rng.randrange(1,4),rng.randrange(3),rng.randrange(2,6)
        n = size+left+right
        w = tuple(rng.choice((-1,1))*rng.randrange(1,n) for _ in range(2))
        z,slot,history = w,left,[(w,left)]
        for _ in range(rng.randint(2,right)):
            for choices in (range(1,slot),range(slot+size+1,n)):
                if choices:
                    z+=(rng.choice((-1,1))*rng.choice(choices),)
            z+=slots(slide(size,1,rng.choice((-1,1))),slot)
            slot+=1
            history.append((z,slot))
        start,end = (w,left,size),(z,slot,size)
        orbit = cohort_orbit(n,start,end,(),0,n)
        chart,split,count = cohort_chart(start,end,(),0,n)
        assert len(orbit.points)==2**count
        candidates = {t for _,t in orbit.points}
        begin = left+size
        for word,index in history:
            actual = cut(braid_image(n,word),index,size)
            # Recover both prefix words from the actual projected reading,
            # then undo only their pure within-cohort spectator braids.
            rel = inv(chart)+word
            before = content(substitute(braid_image(n,inv(chart)),actual.before)).keys()
            pure = ()
            for start_slot,end_slot in ((begin,begin+split),(begin+split,begin+count)):
                num = end_slot-start_slot
                if not num:
                    continue
                beta = restrict(n,rel,set(range(start_slot,end_slot)))
                order = output_order(list(range(num)),tuple(map(abs,beta)))
                take = len(before & set(range(start_slot+1,end_slot+1)))
                chosen = sorted(order[:take])
                template = expose(chosen,num)
                standard = output_order(list(range(num)),tuple(map(abs,template)))
                residual = expose([standard.index(t) for t in order],num)
                assert all(abs(g)!=take for g in residual)
                pure+=slots(beta+inv(residual)+inv(template),start_slot)
            undo = chart+inv(pure)+inv(chart)
            normalized = cut(braid_image(n,undo+word),index,size)
            assert normalized in candidates
            twists+=actual!=normalized
            mixed+=0<split<count
            total+=1
    assert twists and mixed
    return total,mixed,twists


def checks():
    from semistrict_surface_gap_orbits import endpoint_symmetries,positive_example
    from semistrict_surface_three_cycle import bracket,cycle,solve

    total,mixed,twists = validate_paths()
    for side in (None,0,1):
        *_,args = positive_example(2,side,flanks=1)
        calc,s,t,old,new = args
        h,first,_,word = calc.scan(s)
        f = bracket(calc,1,0,2,old,new,first,calc.scan(t)[1])
        cuts = (*old.values(),*new.values())
        assert not any(endpoint_symmetries(calc,q,h,word,cuts) for q in (f.forward,f.backward))
        assert endpoint_symmetries(calc,f.cohorts,h,word,cuts)
        assert len(f.cohorts.points)==4 and len(f.cohorts.generators)==1
        direct = cycle(*args)
        assert direct['surface']==(side is None)
        if side is not None:
            assert direct['open_cycle_schedules']==0
        assert solve(*args)['surface']==(side is None)
    print(f'{total} prescribed-endpoint cuts reconstructed ({mixed} mixed-sign, {twists} changed by pure twists); '
          'both whole-side symmetry tests fail on three positive cyclic inputs, all three decided')


if __name__=='__main__':
    checks()
