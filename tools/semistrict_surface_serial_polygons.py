"""Decide signed positive-polygon comparisons on a causal chain using common unit braids."""
from argparse import ArgumentParser
from pathlib import Path
import json

from semistrict_surface_component_braids import cabling,restrict
from semistrict_surface_history_group import inv
from semistrict_surface_polygon_cabling import rectangle
from semistrict_surface_polygon_grades import resolution
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_signed_width_two import Movies,Presentation,Rule
from semistrict_surface_single_polygon import transport_window
from semistrict_surface_single_power import output_order


def frames(source,graph,flow,reading,records):
    wires = [(-1,i) for i in range(len(source))]
    word,checkpoints = [],{}
    old = iter(records)
    for i,p in reading:
        if p is None:
            a,b = wires[i:i+2]
            off = sum(flow[e] for e in wires[:i])
            word.extend(j+1 for j in rectangle(off,flow[a],flow[b]))
            wires[i:i+2] = b,a
        else:
            h,n,_ = next(old)
            _,ins,outs = graph[p]
            size = sum(flow[e] for e in ins)
            partition = [(e,flow[e]) for e in wires[:i]]+[(p,size)]+[(e,flow[e]) for e in wires[i+len(ins):]]
            checkpoints[p] = (h,tuple(wires),i),partition,len(word)
            wires[i:i+len(ins)] = outs
    return tuple(word),checkpoints


def decide(model,source,first,second,radius=None):
    if model.attachments:
        raise ValueError('the comparison requires a 3-computad')
    u,end = model.parse(source,first)
    v,other = model.parse(source,second)
    if end!=other:
        raise ValueError('expected parallel readings')
    arities = [(len(r.source),len(r.target)) for r in model.pres.rules]
    data = resolution(source,(first,second),arities,'swap')
    if data is None:
        return dict(surface=False,obstruction='named incidence')
    widths,flow,graph,readings = data
    (a,start),(b,finish) = [frames(source,graph,flow,t,r) for t,r in zip(readings,(u,v))]
    width = sum(widths)
    if braid_image(width,a)!=braid_image(width,b):
        return dict(surface=False,obstruction='resolved total braid')
    order = list(start)
    serial = all(set(graph[p][2]).intersection(graph[q][1]) for p,q in zip(order,order[1:]))
    def unsupported(reason):
        return dict(surface=False if serial else None,serial=serial,obstruction=reason)
    if order!=list(finish):
        return unsupported('different named execution orders')
    results = []
    for p in order:
        before,partition,x = start[p]
        after,target,y = finish[p]
        # The unit-frame difference at this checkpoint must transport each
        # live spectator as one packet and the entire polygon as another.
        relative = inv(a[:x])+b[:y]
        lower = a[x:]+inv(b[y:])
        face,keep,off = [],[],0
        for e,size in partition:
            keep.append(off)
            face.append((e,off,off+size))
            off += size
        z = restrict(width,relative,keep)
        labels = [e for e,size in partition]
        if (output_order(labels,tuple(map(abs,z)))!=[e for e,size in target] or
                braid_image(width,cabling(face,z))!=braid_image(width,relative)):
            return unsupported('checkpoint does not preserve its packets')
        upper = restrict(width,lower,keep)
        result = transport_window(model,graph[p][0],before,after,z,upper,radius)
        results.append(result)
        if result['surface'] is False:
            return unsupported(result.get('obstruction','unavailable window transport'))
    yes = True if all(r['surface'] is True for r in results) else None
    return dict(surface=yes,serial=serial,checkpoints=results,resolved_width=width)


def checks():
    from itertools import product
    from collections import defaultdict
    from random import Random
    from semistrict_surface_private_winding import solve as two
    from semistrict_surface_private_three_windings import solve as three
    from semistrict_surface_meridian_transport import solve as wide
    from semistrict_surface_single_polygon import expand
    from semistrict_surface_raw_movie_graph import raw_compare
    # The middle phase of the polygon chain has three strands at its site.
    s = ((0,'a'),)
    rules = [Rule('',s*2,s*3),Rule('',s*3,s),Rule('',s,s*2)]
    model = Movies(Presentation({}, {'a':('','')},rules,{'a':0}),'')
    tested = positive = 0
    for stationary in (1,2,3):
        n = 1+stationary
        for slot in range(n):
            for length in range(4):
                for w in product(range(1,n),repeat=length):
                    finish = output_order(range(n),w).index(slot)
                    def crossings(arity):
                        return [('swap',g-1) for g in expand(n,slot,arity,w)]
                    source = s*(n+1)
                    first = [(0,slot),(1,slot),(2,slot)]+crossings(2)
                    second = crossings(2)+[(0,finish),(1,finish),(2,finish)]
                    result = decide(model,source,first,second)
                    # Independent transport on the original, unexpanded scalar sites.
                    data = dict(edges={},initial=[],start_vertex=0,marks={'a':([],[])},scalar_at={'a':0},
                                higher=[{'p':('a','a')}],history=[(0,'a')]*n,
                                source=[('p',slot)]+[('X',g-1) for g in w],
                                target=[('X',g-1) for g in w]+[('p',finish)])
                    reference = (two if n==2 else three if n==3 else wide)(data)['surface_filler']
                    assert result['serial'] and result['surface']==reference
                    positive += result['surface']
                    tested += 1
    # Different progress at successive vertices: the spectator is between
    # the first and second changes in the original movie.
    initial = s*3
    a = [(0,0),('swap',2),('swap',1),('swap',0),(1,1),(2,1)]
    b = [('swap',1),('swap',0),(0,1),(1,1),(2,1)]
    assert decide(model,initial,a,b)['surface']
    assert raw_compare(model,initial,a,b)['raw']
    assert not decide(model,initial,b,a)['surface']
    # One full twist between two vertices is internal to the protected packet.
    first = [(0,0),('swap',0),('swap',0),(1,0)]
    last = [(0,0),(1,0)]
    assert decide(model,initial,first,last)['surface'] is False
    edges = {'f':(0,1),'g':(1,2),'h':(2,3)}
    marks = {name:(edge,edge) for name,edge in zip('abc','fgh')}
    rules = [Rule('fg',((0,'a'),(1,'b')),((0,'a'),(1,'b'),(0,'a'))),
             Rule('fg',((1,'b'),(0,'a')),((0,'a'),(1,'b'))),
             Rule('gh',((1,'c'),(0,'b')),((0,'b'),(1,'c'))),
             Rule('gh',((0,'b'),(1,'c')),((1,'c'),(0,'b')))]
    planar = Movies(Presentation(edges,marks,rules),'fgh')
    placed = true = 0
    rng = Random(224)
    for word in ('cba','acb','cab','bac'):
        src = tuple(('abc'.index(n),n) for n in word)
        groups = defaultdict(list)
        todo = [(src,(),())]
        while todo:
            h,reading,names = todo.pop()
            if len(names)>=2:
                groups[h,tuple(sorted(names))].append(reading)
            for i in range(len(h)):
                out = planar.swap(h,i,True)
                if out is not None:
                    todo.append((out,reading+(('swap',i),),names))
                if len(names)<3:
                    for rid in range(4):
                        nxt = planar.named(h,rid,i)
                        if nxt is not None:
                            todo.append((nxt[0],reading+((rid,i),),names+(rid,)))
        for choices in groups.values():
            for a,b in product(rng.sample(choices,min(6,len(choices))),repeat=2):
                result = decide(planar,src,a,b)
                if result['surface'] is not None:
                    assert result['surface']==planar.compare(src,a,b)['surface'],(src,a,b,result,planar.compare(src,a,b))
                    placed += 1
                    true += result['surface']
    independent = Movies(Presentation({}, {'a':('','')},[Rule('',s,s)],{'a':0}),'')
    a,b = [(0,0),(0,1)],[(0,1),(0,0)]
    assert decide(independent,s*2,a,b)['surface'] is None
    assert raw_compare(independent,s*2,a,b)['raw']
    return dict(chain_queries=tested,positive=positive,partial_transport_checked=True,positioned_queries=placed,positioned_positive=true)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    parser.add_argument('--radius',type=int)
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        if q.get('attachments'):
            raise ValueError('expected a 3-computad')
        rules=[Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        pres=Presentation(q['edges'],q['marks'],rules,q.get('mark_roots'))
        source=tuple(map(tuple,q['source']))
        pres.walk(q['start'],source,q.get('vertex'))
        result=decide(Movies(pres,q['start']),source,q['first'],q['second'],args.radius)
    else:
        result=checks()
    print(json.dumps(result))
