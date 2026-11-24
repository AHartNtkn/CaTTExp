"""Quotient intermediate packet cuts by tested endpoint braid symmetries."""
from dataclasses import dataclass
from itertools import combinations, permutations, product

from semistrict_surface_component_braids import cabling, restrict
from semistrict_surface_history_group import inv, realize, reduced
from semistrict_surface_meridian_transport import content
from semistrict_surface_packet_meetings import cut, gain_factors
from semistrict_surface_phase_gains import slots, substitute
from semistrict_surface_shared_edge import braid_image


@dataclass(frozen=True)
class Orbit:
    points: tuple
    generators: tuple


def slide(size, count, sign):
    return tuple(sign*g for i in range(count) for g in range(i+size,i,-1))


def expose(order, size):
    remaining = list(range(size))
    path = []
    for dest,name in enumerate(order):
        src = remaining.index(name)
        path.extend(range(src,dest,-1))
        remaining.insert(dest,remaining.pop(src))
    return tuple(path)


def pure_generators(count):
    for i,j in combinations(range(1,count+1),2):
        path = tuple(range(j-1,i,-1))
        yield path+(i,i)+inv(path)


@dataclass(frozen=True)
class Directions:
    forward: Orbit
    backward: Orbit


def gap_orbit(width, source, goal, anchor, offset, gap_width):
    """Bound every checkpoint by two finite lists of spectator-braid orbits."""
    w,i,size = source
    z,j,_ = goal
    old = cut(braid_image(gap_width,w),i,size)
    new = cut(braid_image(gap_width,z),j,size)
    factors = gain_factors(old,new)
    if factors is None:
        return False
    negative,positive = (content(f).keys() for f in factors)

    def family(backward):
        base,slot = (z,j) if backward else (w,i)
        frame = braid_image(gap_width,base)
        chart = reduced(anchor+slots(base,offset))
        count = slot if backward else gap_width-size-slot
        def spectator_slot(k):
            return slot-1-k if backward else slot+size+k
        names = [cut(frame,spectator_slot(k),1).names[0] for k in range(count)]
        eligible = [i for i,name in enumerate(names) if name in negative|positive]
        points = {}
        for length in range(len(eligible)+1):
            for group in combinations(eligible,length):
                # Equal-sign crossings commute with permutations of the
                # collected spectators by block naturality.
                uniform = all(names[k] in negative for k in group) or all(names[k] in positive for k in group)
                for order in (group,) if uniform else permutations(group):
                    braid = list(slots(expose(order,count),size))
                    for k,name_index in enumerate(order):
                        sign = -1 if names[name_index] in negative else 1
                        braid.extend(slots(slide(size,1,-sign if backward else sign),k))
                    if backward:
                        # Reflect the active window only; signs already reversed.
                        braid = [(count+size-abs(g))*(1 if g>0 else -1) for g in braid]
                    start = 0 if backward else slot
                    word = reduced(chart+slots(braid,offset+start))
                    location = slot-length if backward else slot+length
                    point = cut(braid_image(width,word),offset+location,size)
                    points[point] = word
        start = offset if backward else offset+slot+size
        generators = tuple(reduced(chart+slots(g,start)+inv(chart)) for g in pure_generators(count))
        return Orbit(tuple((word,point) for point,word in points.items()),generators)

    return Directions(family(False),family(True))


def macro_loop(calc, history, word):
    face = []
    offset = 0
    for _,e in history:
        size = calc.flow[e]
        face.append((e,offset,offset+size))
        offset += size
    shadow = restrict(offset,word,{a for _,a,_ in face})
    if braid_image(offset,cabling(face,shadow)) != braid_image(offset,word):
        return False
    return realize(history,history,shadow,calc.model.pres.marks) is not None


def fixes(width, word, cuts):
    frame = braid_image(width,word)
    return all(substitute(frame,t.before)==t.before and
               all(substitute(frame,a)==a for a in t.atoms) for t in cuts)


def endpoint_symmetries(calc, orbit, terminal, total, cuts):
    return all(fixes(calc.width,g,cuts) and macro_loop(calc,calc.root,g) and
               macro_loop(calc,terminal,reduced(inv(total)+g+total)) for g in orbit.generators)


def joint_representatives(calc, families, terminal, total, cuts):
    """Return actual candidates and whether they cover all solutions up to symmetry."""
    options = [(f.forward,f.backward) if isinstance(f,Directions) else (f,) for f in families.values()]
    candidates = []
    for combination in product(*options):
        orbits = [f for f in combination if isinstance(f,Orbit)]
        certified = all(endpoint_symmetries(calc,f,terminal,total,cuts) for f in orbits)
        if certified and len(orbits)==2:
            def preserves(first,second):
                return all(fixes(calc.width,g,[t for _,t in first.points]) for g in second.generators)
            a,b = orbits
            certified = preserves(a,b) or preserves(b,a)
        points = {p:f.points if isinstance(f,Orbit) else f for p,f in zip(families,combination)}
        if certified:
            return points,True
        candidates.append(points)
    return candidates[0],False


def check_orbits():
    from random import Random
    from semistrict_surface_single_power import output_order

    rng = Random(3741)
    checked = mixed = 0
    for _ in range(100):
        size, left, right = rng.randrange(1,4), rng.randrange(3), rng.randrange(2,6)
        n = size+left+right
        w = tuple(rng.choice((-1,1))*rng.randrange(1,n) for _ in range(2))
        slot = left
        actions = []
        checkpoints = [(0,w,slot)]
        live = w
        amount = rng.randint(2,right)
        for k in range(amount):
            for side,choices in [('left',range(1,slot)),('right',range(slot+size+1,n))]:
                if choices:
                    g = rng.choice((-1,1))*rng.choice(choices)
                    live += (g,)
                    actions.append((side,g))
            sign = rng.choice((-1,1))
            live += slots(slide(size,1,sign),slot)
            actions.append(('gain',sign))
            slot += 1
            checkpoints.append((len(actions),live,slot))

        family = gap_orbit(n,(w,left,size),(live,slot,size),(),0,n)
        assert isinstance(family,Directions)
        for k,(time,word,loc) in enumerate(checkpoints):
            actual = cut(braid_image(n,word),loc,size)
            for back in (False,True):
                count = slot if back else right
                segment = actions[time:][::-1] if back else actions[:time]
                signs = [g for side,g in segment if side=='gain']
                num = len(signs)
                if back:
                    beta = tuple((slot-abs(g))*(-1 if g>0 else 1) for side,g in segment if side=='left')
                else:
                    beta = tuple((abs(g)-left-size)*(1 if g>0 else -1) for side,g in segment if side=='right')
                perm = output_order(list(range(count)),tuple(map(abs,beta)))
                chosen = list(perm[:num])
                if len(set(signs))<2:
                    chosen.sort()
                else:
                    mixed+=1
                template = expose(chosen,count)
                reference = output_order(list(range(count)),tuple(map(abs,template)))
                residual = expose([reference.index(x) for x in perm],count)
                assert all(abs(g)!=num for g in residual)
                pure = beta+inv(residual)+inv(template)
                assert list(output_order(list(range(count)),tuple(map(abs,pure)))) == list(range(count))
                if back:
                    pure = tuple((count-abs(g))*(1 if g>0 else -1) for g in pure)
                base,off = (live,0) if back else (w,left+size)
                undo = base+slots(inv(pure),off)+inv(base)
                recovered = cut(braid_image(n,undo+word),loc,size)
                points = family.backward.points if back else family.forward.points
                assert recovered in {t for _,t in points}, (back,k,actual)
                checked+=1
    assert mixed
    return checked,mixed


def positive_example(number, side):
    from semistrict_surface_signed_width_two import Movies,Presentation,Rule
    from semistrict_surface_polygon_grades import resolution
    from semistrict_surface_signed_meetings import Signed,ordinary,verify_original
    from semistrict_surface_phase_gains import signature
    s = ((0 if side is None else side,'s'),)
    path = '' if side is None else 'f'
    model = Movies(Presentation({'f':(0,0)},{'s':('','')},[Rule(path,s,s)]*3,{'s':0}),path)
    root = s*(number+3)
    def movie(stages):
        packets = [(1,1),(0,number+1),(2,1)]
        word = []
        for exchanges,p in stages:
            for g in exchanges:
                face,off = [],0
                for name,size in packets:
                    face.append((name,off,off+size))
                    off += size
                word.extend(('swap',k-1) for k in cabling(face,(g,)))
                packets[g-1],packets[g]=packets[g],packets[g-1]
            if p is not None:
                pos = next(i for i,(name,_) in enumerate(packets) if name==p)
                word.append((p,sum(k for _,k in packets[:pos])))
        return tuple(word)
    x = movie([((1,),0),((1,),1),((2,1),2)])
    y = movie([((),2),((2,1),0),((2,),1),((2,),None)])
    assert verify_original(model,root,x)==verify_original(model,root,y)
    data = resolution(root,(ordinary(x),ordinary(y)),[(1,1)]*3,'swap')
    calc = Signed(model,root,data)
    a,b = [calc.decode(i,t) for i,t in zip((x,y),data[-1])]
    old,new = [signature(calc,v)[1] for v in (a,b)]
    return model,root,x,y,(calc,a,b,old,new)


def checks():
    from semistrict_surface_raw_movie_graph import raw_compare
    from semistrict_surface_three_cycle import bracket,cycle,solve
    checked,mixed = check_orbits()
    from types import SimpleNamespace
    from semistrict_surface_signed_width_two import Movies,Presentation
    pres = Presentation({'f':(0,0)},{'a':('',''),'b':('','')},[],{'a':0,'b':0})
    positioned = SimpleNamespace(model=Movies(pres,'f'),flow={'a':1,'b':1})
    assert macro_loop(positioned,((0,'a'),(0,'b')),(1,1))
    assert not macro_loop(positioned,((0,'a'),(1,'b')),(1,1))
    assert not fixes(2,(1,1),[cut(braid_image(2,()),0,1)])
    for size in (2,3):
        for side in (None,0,1):
            model,root,x,y,args = positive_example(size,side)
            calc,a,b,old,new = args
            h,first,_,total = calc.scan(a)
            family = bracket(calc,1,0,2,old,new,first,calc.scan(b)[1])
            assert len(family.forward.points)==2**size
            assert endpoint_symmetries(calc,family.forward,h,total,(*old.values(),*new.values()))
            direct = cycle(*args)
            assert direct['surface']==(side is None)
            assert solve(*args)['surface']==(side is None)
            if side is None:
                # The signed stationary relation allows either spelling of
                # the same pure prefix, so these two prefixed faces still lift.
                initial = (('swap',1),('swap',0),('swap',1))*12
                final = (('swap',0),('swap',1),('swap',0))*12
                assert braid_image(3,tuple(i+1 for _,i in initial))==braid_image(3,tuple(i+1 for _,i in final))
                assert not raw_compare(model,root,initial+x,final+y)['raw']
                # A twist around the first two incoming spectators produces
                # distinct intermediate meridians at exactly the same endpoints.
                g = family.forward.generators[0]
                words = [w for w,t in family.forward.points if len(content(t.before))==len(content(old[0].after))+1]
                counts = [len({cut(braid_image(calc.width,g*k+w),len(content(old[0].after))+1,
                                   len(old[1].names)) for k in range(12)}) for w in words]
                assert max(counts)==12
            else:
                assert direct['open_cycle_schedules']==0
    print(f'{checked} intermediate orbits reconstructed in both directions ({mixed} mixed-sign checks); '
          'six positive old comparisons decided, four negatives and two further surface-only prefixed cases')


if __name__ == '__main__':
    checks()
