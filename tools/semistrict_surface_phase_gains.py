"""Decide whether each polygon needs at most one prism, in arbitrary chronological order."""
from argparse import ArgumentParser
from collections import deque
import json
from pathlib import Path

from semistrict_surface_component_braids import restrict
from semistrict_surface_history_group import inv
from semistrict_surface_joint_labels import positive_normal
from semistrict_surface_packet_meetings import cut
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


def gain(calc,movie,k,desired,target_cut):
    boxes,seams=movie
    p,i=boxes[k]
    _,records,places,_=calc.scan(movie)
    old,_,_=records[p]
    after,_,_=desired[p]
    relative=inv(old)+after
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
    shadow=restrict(calc.width,relative,first[i+a:])
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


def decide(model,source,first,second):
    if model.attachments:
        raise ValueError('expected a positive 3-computad')
    pos=ordinary(first),ordinary(second)
    if verify_original(model,source,first)!=verify_original(model,source,second):
        raise ValueError('expected parallel readings')
    arities=[(len(r.source),len(r.target)) for r in model.pres.rules]
    data=resolution(source,pos,arities,'swap')
    def no(reason):
        return dict(one_per_polygon=False,surface=False,obstruction=reason)
    if data is None:
        return no('named incidence')
    calc=Signed(model,source,data)
    start,goal=[calc.decode(w,r) for w,r in zip((first,second),data[-1])]
    h,initial,lower,total=signature(calc,start)
    end,final,upper,last=signature(calc,goal)
    if h!=end or total!=last:
        return no('resolved total or final names')
    desired=calc.scan(goal)[1]
    changed=set()
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
        changed.add(p)
        choices=[s for s in bundles if s<=gained]
        if set().union(*choices)!=gained:
            return no('gained units have no wire cover')
        if set().union(*(s for s in choices if s!=gained))==gained:
            forced=False
        if gained not in choices:
            eligible=False
    if not eligible:
        return dict(one_per_polygon=False,surface=None if not forced else False,
                    obstruction='a polygon requires several gains')
    target_order=tuple(p for p,_ in goal[0])
    def key(movie,done): return tuple(p for p,_ in movie[0]),done
    start_key=key(start,frozenset())
    todo=deque([(start,start_key)])
    seen={start_key:None}
    while todo:
        movie,current=todo.popleft()
        order,done=current
        if order==target_order and done==changed:
            moves=[]
            while seen[current] is not None:
                current,step=seen[current]
                moves.append(step)
            return dict(one_per_polygon=True,surface=True,phase_states=len(seen),actions=moves[::-1])
        def put(m,updated,step):
            new=key(m,updated)
            if new not in seen:
                seen[new]=current,step
                todo.append((m,new))
        for k,p in enumerate(order):
            if p in changed-done and (order,done|{p}) not in seen:
                candidate=gain(calc,movie,k,desired,final[p])
                if candidate is not None:
                    put(candidate,done|{p},('gain',p))
        for k,(p,q) in enumerate(zip(order,order[1:])):
            other=order[:k]+(q,p)+order[k+2:]
            if (other,done) not in seen:
                candidate=calc.exchange(movie,k)
                if candidate is not None:
                    put(candidate,done,('meet',p,q))
    return dict(one_per_polygon=False,surface=False if forced else None,phase_states=len(seen),
                obstruction='no one-gain phase schedule')


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
    return dict(**cut_checks(),changing_splits=positive,padded_splits=padded,
                private_decisions=questions,private_yes=accepted,width_two_decisions=queries,width_two_yes=yes)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        if q.get('attachments'): raise ValueError('expected a 3-computad')
        rules=[Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        model=Movies(Presentation(q['edges'],q['marks'],rules,q.get('mark_roots')),q['start'])
        source=tuple(map(tuple,q['source']))
        model.pres.walk(model.start,source,q.get('vertex'))
        ans=decide(model,source,q['first'],q['second'])
    else:
        ans=checks()
    print(json.dumps(ans))
