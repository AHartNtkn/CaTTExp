"""Decide signed polygon comparisons with one gain per occurrence or per crossing sign."""
from argparse import ArgumentParser
from collections import deque
from functools import lru_cache
import json
from pathlib import Path

from semistrict_surface_component_braids import restrict
from semistrict_surface_history_group import inv
from semistrict_surface_joint_labels import positive_normal
from semistrict_surface_meridian_transport import content,prod,quasi
from semistrict_surface_packet_meetings import Packet,cut,gain_factors
from semistrict_surface_polygon_grades import resolution
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_signed_meetings import Signed,follow,ordinary,orthogonal,verify_original
from semistrict_surface_signed_width_two import Movies,Presentation,Rule
from semistrict_surface_single_power import output_order
from semistrict_surface_stationary_polygons import coset,initial_atoms,passive_prefix,spelling,strip_atom
from semistrict_surface_transfer_cables import cables


def join(n,a,b):
    right,_ = orthogonal(n,inv(a)+b)
    return a+right


def meet(n,a,b):
    x,y = positive_normal(n,a),positive_normal(n,b)
    common = []
    while x and y:
        both = initial_atoms(x) & initial_atoms(y)
        if not both:
            break
        g = min(both)
        x,y = strip_atom(n,x,g),strip_atom(n,y,g)
        common.append(g)
    return tuple(common)


def executable_cut(model,h,w,slot,size):
    """Realize a prescribed ambient prefix coset, including when w itself cannot execute."""
    n=len(h)
    b,a = orthogonal(n,w[::-1])
    a,b = a[::-1],b[::-1]
    _,q = orthogonal(n,w)
    lo = tuple(reversed(spelling(coset(n,b,slot,slot+size))))
    hi = b+passive_prefix(n,q,slot,slot+size)[0]
    member = meet(n,join(n,a,lo),hi)
    u,v = orthogonal(n,inv(a)+member)
    word = u+inv(v)
    h1=h
    for g in word:
        h1=model.swap(h1,abs(g)-1,g>0)
        if h1 is None:
            return None
    return word


def slots(word,offset):
    return tuple(g+(offset if g>0 else -offset) for g in word)


def signature(calc,movie):
    h,records,_,total=calc.scan(movie)
    cuts={}
    sets={}
    for p,(w,i,k) in records.items():
        cuts[p] = cut(braid_image(calc.width,w),i,k)
        names = output_order(range(calc.width),tuple(map(abs,w)))
        sets[p] = frozenset(names[:i])
    return h,cuts,sets,braid_image(calc.width,total)


def substitute(frame,word):
    return prod(*(frame[abs(x)-1] if x>0 else inv(frame[-x-1]) for x in word))


@lru_cache(maxsize=1024)
def first_slot_braid(n,atom):
    """Find an ambient word for the specified first meridian, after deciding existence."""
    names=content(atom)
    if len(names)!=1 or next(iter(names.values()))!=1:
        return None
    if not quasi(atom) or not quasi(prod(inv(atom),tuple(range(1,n+1)))):
        return None
    if len(atom)==1:
        return tuple(-j for j in range(atom[0]-1,0,-1))
    # Left action on a single free word suffices. The compatible conjugate
    # factorizations of the meridian and its complement form a braid frame.
    actions=[(g,braid_image(n,(g,))) for i in range(1,n) for g in (i,-i)]
    seen={atom}
    todo=deque([(atom,())])
    while todo:
        v,path=todo.popleft()
        for g,frame in actions:
            u=substitute(frame,v)
            if u==(1,):
                return path+(-g,)
            if u not in seen:
                seen.add(u)
                todo.append((u,path+(-g,)))
    raise AssertionError('compatible first meridian has no ambient frame')


def gain(calc,movie,k,target_cut,goal_prefix=None):
    boxes,seams=movie
    p,i=boxes[k]
    _,records,places,_=calc.scan(movie)
    old,start,size=records[p]
    h,_=places[p]
    rule=calc.model.pres.rules[p]
    a,b=len(rule.source),len(rule.target)
    first=[]
    offset=0
    for _,e in h:
        first.append(offset)
        offset+=calc.flow[e]
    # Retain one unit from each wire currently to the right of the box.
    # In that chart the gained spectator must occupy the first slot.
    right=h[i+a:]
    if not right:
        return None
    if goal_prefix is not None:
        shadow=restrict(calc.width,inv(old)+goal_prefix,first[i+a:])
    else:
        # In the current basis, the gain factor is the product of the
        # exposed spectator's units. Forgetting all but one chooses its
        # actual first-slot meridian on the right macro chart.
        current=cut(braid_image(calc.width,old),start,size)
        factor=prod(inv(current.after),target_cut.after)
        local=substitute(braid_image(calc.width,inv(old)),factor)
        keep={v+1:j+1 for j,v in enumerate(first[i+a:])}
        atom=prod(tuple(keep[abs(x)]*(1 if x>0 else -1) for x in local if abs(x) in keep))
        shadow=first_slot_braid(len(right),atom)
        if shadow is None:
            return None
    exposed=executable_cut(calc.model,right,shadow,0,1)
    if exposed is None:
        return None
    on_input=slots(exposed,i+a)
    on_output=slots(exposed,i+b)
    contact=follow(calc.model,h,on_input)
    _,off=calc.model.named(contact,p,i)
    for word in calc.model.prism_words(contact,p,i,off):
        sign=1 if word[0]>0 else -1
        dual=tuple(sign*j for j in range(i+b,i,-1))
        # Compensate both passive exposure and the gain on the output side.
        paths=seams[:k]+(seams[k]+on_input+word,inv(dual)+inv(on_output)+seams[k+1])+seams[k+2:]
        candidate=boxes[:k]+((p,i+1),)+boxes[k+1:],paths
        _,r,_,_=calc.scan(candidate)
        prefix,slot,size=r[p]
        if cut(braid_image(calc.width,prefix),slot,size)==target_cut:
            return candidate
    return None


def intermediate(source,v,negative):
    atoms=tuple(prod(inv(v),a,v) for a in source.atoms) if negative else source.atoms
    return Packet(prod(source.after,v,inv(prod(*atoms))),atoms)


def decide(model,source,first,second,split_signs=False,separate_runs=False,radius=None):
    criterion='mixed_runs' if separate_runs else 'one_per_sign' if split_signs else 'one_per_polygon'
    if model.attachments:
        raise ValueError('expected a positive 3-computad')
    pos=ordinary(first),ordinary(second)
    if verify_original(model,source,first)!=verify_original(model,source,second):
        raise ValueError('expected parallel readings')
    arities=[(len(r.source),len(r.target)) for r in model.pres.rules]
    data=resolution(source,pos,arities,'swap')
    def no(reason):
        return {criterion:False,'surface':False,'obstruction':reason}
    if data is None:
        return no('named incidence')
    calc=Signed(model,source,data)
    start,goal=[calc.decode(w,r) for w,r in zip((first,second),data[-1])]
    h,initial,lower,total=signature(calc,start)
    end,final,upper,last=signature(calc,goal)
    if h!=end or total!=last:
        return no('resolved total or final names')
    desired=calc.scan(goal)[1]
    grouped=set()
    if separate_runs:
        from semistrict_surface_pair_runs import meeting_arrows,middle_polygons
        grouped=initial.keys()-middle_polygons(meeting_arrows(initial,final))
    routes={}
    forced=True
    scopes=cables(list(data[1]),data[2],data[2])
    # cables() indexes units by initial wire and within-wire offset, whereas
    # prefix permutations use consecutive integers in the same order.
    numbering={u:j for j,u in enumerate(u for _,e in calc.root for u in scopes[e])}
    bundles=[{numbering[u] for u in wire} for wire in scopes.values()]
    eligible=True
    for p in initial:
        if not lower[p]<=upper[p]:
            return no('a preceding unit is lost')
        gained=upper[p]-lower[p]
        if not gained:
            if initial[p]!=final[p]:
                return no('stationary packet cut')
            continue
        cohorts=[gained]
        route={0:[(1,final[p])]}
        if split_signs:
            factors=gain_factors(initial[p],final[p])
            if factors is None:
                return no('packet meridian transport')
            if p in grouped:
                routes[p]=route
                continue
            neg,pos=factors
            cohorts=[{e-1 for e in content(f)} for f in factors if f]
            if len(cohorts)==2:
                # If the positive gain comes first its factor conjugates
                # the collected positive factor by the unique negative one.
                positive_first=prod(neg,pos,inv(neg))
                candidates=[intermediate(initial[p],neg,True),
                            intermediate(initial[p],positive_first,False)]
                route={0:[(j,t) for j,t in enumerate(candidates,2)],
                       2:[(1,final[p])],3:[(1,final[p])]}
        routes[p]=route
        for cohort in cohorts:
            choices=[s for s in bundles if s<=cohort]
            if set().union(*choices)!=cohort:
                return no('gained units have no wire cover')
            if set().union(*(s for s in choices if s!=cohort))==cohort:
                forced=False
            if cohort not in choices:
                eligible=False
    if not eligible:
        return {criterion:False,'surface':None if not forced else False,
                'obstruction':'a gain cohort requires several spectators'}
    target_order=tuple(p for p,_ in goal[0])
    moving=tuple(routes)
    index={p:j for j,p in enumerate(moving)}
    def key(movie,phases): return tuple(p for p,_ in movie[0]),phases
    start_key=key(start,(0,)*len(moving))
    todo=deque([(start,start_key)])
    seen={start_key:None}
    unresolved=False
    while todo:
        movie,current=todo.popleft()
        order,phases=current
        if order==target_order and all(j==1 for j in phases):
            moves=[]
            while seen[current] is not None:
                current,step=seen[current]
                moves.append(step)
            return {criterion:True,'surface':True,'phase_states':len(seen),'actions':moves[::-1]}
        def put(m,updated,step):
            new=key(m,updated)
            if new not in seen:
                seen[new]=current,step
                todo.append((m,new))
        for k,p in enumerate(order):
            if p not in routes:
                continue
            j=index[p]
            for stage,target in routes[p].get(phases[j],()):
                updated=phases[:j]+(stage,)+phases[j+1:]
                if (order,updated) not in seen:
                    prefix=desired[p][0] if stage==1 else None
                    if p in grouped:
                        from semistrict_surface_gain_runs import run
                        candidate,unknown=run(calc,movie,k,prefix,target,radius)
                        unresolved|=unknown
                    else:
                        candidate=gain(calc,movie,k,target,prefix)
                    if candidate is not None:
                        put(candidate,updated,('run' if p in grouped else 'gain',p))
        for k,(p,q) in enumerate(zip(order,order[1:])):
            other=order[:k]+(q,p)+order[k+2:]
            if (other,phases) not in seen:
                candidate=calc.exchange(movie,k)
                if candidate is not None:
                    put(candidate,phases,('meet',p,q))
    return {criterion:None if unresolved else False,'surface':False if forced and not unresolved else None,'phase_states':len(seen),
            'obstruction':'no permitted gain schedule'}


def cut_checks():
    from itertools import product
    from semistrict_surface_history_group import realize
    from semistrict_surface_one_step_reflection import quotient
    # Names a and b occupy disjoint positive-width sites. The third event is
    # a scalar before, between, or after them. Enumerate all reachable ends.
    marks={'a':('f','f'), 'b':('g','g'), 's':('','')}
    model=Movies(Presentation({'f':(0,0),'g':(0,0)},marks,[],{'s':0}),'fg')
    checked=realized=alternative=0
    for gap in range(3):
        root=((0,'a'),(1,'b'),(gap,'s'))
        ends={root}
        todo=[root]
        while todo:
            h=todo.pop()
            for g in (-2,-1,1,2):
                other=model.swap(h,abs(g)-1,g>0)
                if other is not None and other not in ends:
                    ends.add(other)
                    todo.append(other)
        for length in range(4):
            for w in product((-2,-1,1,2),repeat=length):
                _,a=orthogonal(3,w[::-1])
                a=a[::-1]
                top=a+orthogonal(3,w)[0]
                paths=[()]
                seen=set()
                feasible=set()
                for d in paths:
                    x=inv(a)+d
                    if any(realize(root,h,x,marks) is not None for h in ends):
                        feasible.add(braid_image(3,x))
                    for g in (1,2):
                        z=d+(g,)
                        b=braid_image(3,z)
                        if b not in seen and quotient(z,top) is not None:
                            seen.add(b)
                            paths.append(z)
                for slot,size in ((0,1),(1,1),(2,1),(0,2),(1,2)):
                    target=cut(braid_image(3,w),slot,size)
                    oracle=any(cut(f,slot,size)==target for f in feasible)
                    u=executable_cut(model,root,w,slot,size)
                    assert oracle==(u is not None)
                    if oracle:
                        assert follow(model,root,u) in ends and cut(braid_image(3,u),slot,size)==target
                        realized+=1
                        alternative+=not any(realize(root,h,w,marks) is not None for h in ends)
                    checked+=1
    assert 0<alternative<realized<checked
    return dict(cut_queries=checked,executable_cuts=realized,illegal_representatives=alternative)


def opposite_checks():
    from itertools import product
    from semistrict_surface_link_schedules import decide as counts
    from semistrict_surface_raw_movie_graph import raw_compare,steps
    s=((0,'s'),)
    bubble=((0,'b'),(0,'d'))
    def model(window):
        return Movies(Presentation({'f':(0,0)},{'s':('',''),'b':('','f'),'d':('f','')},
                     [Rule(window,s,bubble),Rule('',s,s)],{'s':0,'b':0}),window)
    def literal(w):
        return tuple(('swap' if g>0 else 'inverse',abs(g)-1) for g in w)
    x=steps((1,0,1,0))+((0,0),(1,3))+steps((2,1,0))
    y=steps((0,1))+((1,2),)+steps((0,1))+((0,2),)+steps((0,1,2))
    m=model('')
    direct=decide(m,s*3,x,y,True)
    assert direct['actions']==[('gain',0),('meet',0,1),('gain',0)]
    assert m.compare(s*3,x,y)['surface'] and not raw_compare(m,s*3,x,y)['raw']
    assert counts(m,s*3,x,y)['surface'] is None and decide(m,s*3,x,y)['surface'] is None
    padded=decide(model('f'),s*3,x,y,True)
    assert padded['surface'] is False
    # Each target below is constructed by two literal native gains. The
    # passive input and output spellings can have genuinely nonabelian order.
    witnesses=0
    for order,u,v in product((-1,1),((),(1,),(1,1,2,2),(2,2,1,1),(-2,-1,2,1)),
                              ((),(1,),(-1,-1))):
        before=slots(u,1)+(order,)+slots(v,2)+(-order*2,)
        after=inv((-order*3,-order*2))+inv(slots(v,3))+inv((order*2,order))+inv(slots(u,2))
        z=literal(before)+((0,2),)+literal(after)
        assert decide(m,s*4,((0,0),),z,True)['surface'] is True
        witnesses+=1
    # Independent first-slot realization in B2: at length <=7 the two
    # powers of each exponent magnitude suffice since B2 is infinite cyclic
    # and the meridian lengths grow by four every additional full twist.
    targets={braid_image(2,((1 if k>=0 else -1),)*abs(k))[0] for k in range(-12,13)}
    basis=(1,2)
    cases=accepted=0
    for depth in range(4):
        for z in product((-2,-1,1,2),repeat=depth):
            for e in basis:
                atom=prod(z,(e,),inv(z))
                result=first_slot_braid(2,atom)
                assert (result is not None)==(atom in targets)
                if result is not None:
                    assert braid_image(2,result)[0]==atom
                    accepted+=1
                cases+=1
    assert 0<accepted<cases
    return dict(mixed_witness=direct,padded_negative=padded,explicit_signed_comparisons=witnesses,
                cyclic_meridian_queries=cases,cyclic_meridians_realized=accepted)


def checks():
    from itertools import product
    from random import Random
    from semistrict_surface_link_schedules import decide as counts
    from semistrict_surface_polygon_cabling import rectangle
    from semistrict_surface_raw_movie_graph import raw_compare,steps
    from semistrict_surface_private_divisor_movies import solve as private
    s=((0,'s'),)
    ports={'s':('',''),'b':('','f'),'d':('f','')}
    def splits(window):
        return Movies(Presentation({'f':(0,0)},ports,[Rule(window,s,((0,'b'),(0,'d')))],
                                  {'s':0,'b':0}),window)
    first=steps((1,0,1))+((0,0),)+steps(rectangle(0,2,1))+((0,0),)
    last=steps((0,1,0))+((0,1),)+steps(rectangle(0,1,2))+((0,2),)
    m=splits('')
    positive=decide(m,s*3,first,last)
    assert positive['actions']==[('gain',0),('meet',0,1),('gain',1)]
    assert m.compare(s*3,first,last)['surface'] and not raw_compare(m,s*3,first,last)['raw']
    assert counts(m,s*3,first,last)['surface'] is None
    assert decide(m,s*3,last,first)['surface'] is False
    padded=decide(splits('f'),s*3,first,last)
    assert not padded['one_per_polygon'] and padded['surface'] is None
    unary=Movies(Presentation({}, {'s':('','')},[Rule('',s,s)],{'s':0}),'')
    twice=decide(unary,s*3,((0,0),)+steps((0,1)),steps((0,1))+((0,2),))
    assert twice['surface'] is None and not twice['one_per_polygon']
    # An independent private-divisor decision on positive unary readings.
    # Distribute two labelled updates on the three strands of a common braid,
    # with each checkpoint allowed before, between or after its crossings.
    rng=Random(8491)
    data=dict(edges={},initial=[],start_vertex=0,scalar_at={'s':0},marks={'s':[[],[]]},
              higher=[{'p':['s','s']}],history=s*3)
    questions=accepted=0
    for word in ((0,1,0),(0,0,1,1),(1,0,1,0)):
        def sample():
            slots=sorted(rng.choices(range(len(word)+1),k=2))
            names=rng.sample(range(3),2)
            order=list(range(3))
            reading=[]
            for k in range(len(word)+1):
                for j,slot in enumerate(slots):
                    if slot==k:
                        reading.append((0,order.index(names[j])))
                if k<len(word):
                    i=word[k]
                    reading.append(('swap',i))
                    order[i],order[i+1]=order[i+1],order[i]
            return tuple(reading)
        def private_word(w):
            return [('X' if p=='swap' else 'p',i) for p,i in w]
        for _ in range(120):
            x,y=sample(),sample()
            answer=decide(unary,s*3,x,y)
            if answer['surface'] is None:
                continue
            exact=private(dict(data,source=private_word(x),target=private_word(y)))
            assert exact['surface_filler']==answer['surface'],(x,y,answer,exact)
            questions+=1
            accepted+=answer['surface']
    assert 0<accepted<questions
    # Exact width-two engine changes a wire's placement between the ends of f.
    moving=Movies(Presentation({'f':(0,0)},{'s':('','')},
                  [Rule('f',s,((1,'s'),)),Rule('f',((1,'s'),),s)],{'s':0}),'f')
    queries=yes=0
    grouped={}
    todo=[(s*2,())]
    while todo:
        h,w=todo.pop()
        grouped.setdefault(h,[]).append(w)
        if len(w)==4: continue
        t=moving.swap(h,0,True)
        if t is not None: todo.append((t,w+(('swap',0),)))
        for i,p in product(range(2),repeat=2):
            r=moving.named(h,p,i)
            if r is not None: todo.append((r[0],w+((p,i),)))
    for group in grouped.values():
        for x in group:
            for y in rng.sample(group,min(6,len(group))):
                answer=decide(moving,s*2,x,y)
                assert answer['surface']==moving.compare(s*2,x,y)['surface']
                yes+=answer['surface']
                queries+=1
    return dict(**cut_checks(),**opposite_checks(),changing_splits=positive,padded_splits=padded,
                private_decisions=questions,private_yes=accepted,width_two_decisions=queries,width_two_yes=yes)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    parser.add_argument('--opposite-signs',action='store_true',help='allow one gain of each sign per polygon')
    parser.add_argument('--separate-runs',action='store_true',help='group unrestricted gains outside transitive triangles')
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        if q.get('attachments'): raise ValueError('expected a 3-computad')
        rules=[Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        model=Movies(Presentation(q['edges'],q['marks'],rules,q.get('mark_roots')),q['start'])
        source=tuple(map(tuple,q['source']))
        model.pres.walk(model.start,source,q.get('vertex'))
        ans=decide(model,source,q['first'],q['second'],split_signs=args.opposite_signs or args.separate_runs,
                   separate_runs=args.separate_runs)
    else:
        ans=checks()
    print(json.dumps(ans))
