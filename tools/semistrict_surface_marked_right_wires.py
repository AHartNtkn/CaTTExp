"""Positive shared transfers with arbitrary private left polygons and unary right changes."""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import product
import json
from pathlib import Path
from graphlib import TopologicalSorter

from semistrict_surface_planar_cylinder import moves, parse
from semistrict_surface_total_ports import compare_incidence, incidence


def phases(word, markers):
    """For each crossing edge, count the markers before its occurrence."""
    result = {}
    k = 0
    for i,e in enumerate(word):
        while k<len(markers) and markers[k][1]<=i:
            k += 1
        result[e] = k
    assert len(result)==len(word)
    return result


def schedule(graph,starts,ends,u,v,placements,drops):
    """Order all f-diagram operations together and check the original wire redexes."""
    order = TopologicalSorter()
    words = {f:list(w) for f,w in starts.items()}
    gaps = {}
    fresh = 0
    def interval(f,e,lo,hi):
        order.add(('e',e),('gap',f,lo))
        order.add(('gap',f,hi),('e',e))
    for f,word in words.items():
        gaps[f] = list(range(fresh,fresh+len(word)+1))
        fresh += len(word)+1
        for i,e in enumerate(word):
            interval(f,e,gaps[f][i],gaps[f][i+1])
    per_polygon = defaultdict(list)
    for p,f,j in placements:
        _,ins,outs = graph[p]
        per_polygon[p].append((f,j))
        i = words[f].index(ins[0])
        assert tuple(words[f][i:i+len(ins)])==ins
        borders = [gaps[f][i],*range(fresh,fresh+len(outs)-1),gaps[f][i+len(ins)]]
        fresh += len(outs)-1
        for e in ins:
            order.add(('p',p),('e',e))
        for k,e in enumerate(outs):
            order.add(('e',e),('p',p))
            interval(f,e,borders[k],borders[k+1])
        words[f][i:i+len(ins)] = outs
        gaps[f][i:i+len(ins)+1] = borders
    assert words==ends
    words = {f:list(w) for f,w in starts.items()}
    heights = {f:[h for _,h in u[f]] for f in words}
    replay = []
    for node in order.static_order():
        if node[0]=='gap':
            continue
        _,item = node
        if node[0]=='e':
            for f,j in drops[item]:
                h = heights[f][j]
                assert words[f][h]==item and (j+1==len(heights[f]) or h<heights[f][j+1])
                heights[f][j] += 1
                replay.append(('right',f,j,item))
        else:
            _,ins,outs = graph[item]
            for f,phase in per_polygon[item]:
                i = words[f].index(ins[0])
                assert tuple(words[f][i:i+len(ins)])==ins
                assert sum(h<=i for h in heights[f])==phase
                assert all(h<=i or h>=i+len(ins) for h in heights[f])
                words[f][i:i+len(ins)] = outs
                heights[f] = [h if h<=i else h+len(outs)-len(ins) for h in heights[f]]
                replay.append(('left',item,f))
    assert words==ends and all(h==[i for _,i in v[f]] for f,h in heights.items())
    return replay


def solve(source,right,traces,anchored,unary):
    ids = {}
    markers = [defaultdict(list),defaultdict(list)]
    a,b = [incidence(source,right,trace,ids,unary,place) for trace,place in zip(traces,markers)]
    u,v = markers
    if {f:[n for n,_ in row] for f,row in u.items()} != {f:[n for n,_ in row] for f,row in v.items()}:
        return None
    wires = [f for f,side in a[1].items() if side]
    starts = {f:list(a[3][f]) for f in wires}
    initial = {f:phases(starts[f],u[f]) for f in wires}
    steps = compare_incidence(a,b,anchored)
    if steps is None:
        return None
    current = initial
    right_moves = 0
    placement = []
    drops = defaultdict(list)
    for p,f in steps:
        _,ins,outs = a[2][p]
        incoming = [current[f].pop(e) for e in ins]
        phase = min(incoming)
        placement.append((p,f,phase))
        for e,value in zip(ins,incoming):
            drops[e].extend((f,j) for j in reversed(range(phase,value)))
        right_moves += sum(value-phase for value in incoming)
        current[f].update(dict.fromkeys(outs,phase))
    for f in wires:
        final = phases(b[3][f],v[f])
        assert current[f].keys()==final.keys()
        for e,phase in final.items():
            if phase>current[f][e]:
                return None
            drops[e].extend((f,j) for j in reversed(range(phase,current[f][e])))
            right_moves += current[f][e]-phase
    replay = schedule(a[2],starts,{f:list(b[3][f]) for f in wires},u,v,placement,drops)
    return dict(left_prisms=len(steps), right_prisms=right_moves, phases=placement, schedule=replay)


def private_right(rules,right,anchored):
    result = set()
    for name,l,r in rules:
        if name!='swap' and name not in anchored and all(x in right for x in l+r):
            if len(l)!=1 or len(r)!=1:
                raise ValueError('private right rules must be unary')
            result.add(name)
    return result


def checks():
    from semistrict_surface_signed_width_two import Movies, Presentation, Rule
    from semistrict_surface_raw_movie_graph import raw_compare
    from semistrict_surface_square_mutex import diagram
    comparisons = positive = prism_uses = 0
    cases = [
        ('Ba',[('p','a','aa'),('q','B','C'),('across','a','BB'),('back','C','aa')],3),
        ('Baa',[('p','aa','aa'),('q','B','C'),('gate','aC','Ca')],3),
        ('BaB',[('p','a','aa'),('join','aa','x'),('q','B','C'),('anchor','x','B')],3),
        ('BBa',[('p','a','aa'),('q','B','C'),('rev','aC','Ca'),('transfer','C','x')],2),
    ]
    for s,rs,budget in cases:
        source = tuple(s)
        rules = [(n,tuple(l),tuple(r)) for n,l,r in rs]
        right = set('BC')
        unary = private_right(rules,right,set())
        def history(w):
            return tuple((int(c in right),c) for c in w)
        marks = {c: (('g','g') if c in right else ('f','f')) for c in 'aBxC'}
        placed = []
        for n,l,r in rules:
            sides = {c in right for c in l+r}
            if len(sides)==2:
                placed.append(Rule('fg',history(l),history(r)))
            else:
                placed.append(Rule('g' if True in sides else 'f',tuple((0,c) for c in l),tuple((0,c) for c in r)))
        model = Movies(Presentation({'f':(0,1),'g':(1,2)},marks,placed),'fg')
        names = {n:i for i,(n,_,_) in enumerate(rules)}
        groups = defaultdict(dict)
        ids = {}
        todo = [(source,(),(),0)]
        while todo:
            w,trace,path,used = todo.pop()
            key = tuple(sorted(i for i,_ in path if i!='swap'))
            shape = diagram(source,trace,False,ids)
            if shape in groups[w,key]:
                continue
            groups[w,key][shape] = trace,path
            for n,i,l,r,out in moves(w,rules,right):
                k = used+(n!='swap')
                if k<=budget:
                    todo.append((out,trace+((n,i,l,r),),path+((names.get(n,n),i),),k))
        for group in groups.values():
            for (a,x),(b,y) in product(group.values(),repeat=2):
                ans = solve(source,right,(a,b),set(),unary)
                expect = ans is not None
                assert model.compare(history(source),x,y)['surface']==expect
                assert raw_compare(model,history(source),x,y)['raw']==expect
                comparisons += 1
                positive += expect
                if ans:
                    prism_uses += ans['left_prisms']+ans['right_prisms']
    # The right change stays strictly inside both sides of the left polygon.
    rules = [('p',tuple('aa'),tuple('xx')),('q',('B',),('C',))]
    source,right = tuple('Baa'),set('BC')
    first = [('swap',0),('q',1),('swap',1),('p',0)]
    second = [('p',1),('swap',0),('q',1),('swap',1)]
    traces = [parse(source,rules,right,w)[1] for w in (first,second)]
    assert solve(source,right,traces,set(),{'q'}) is None
    return dict(comparisons=comparisons,positive=positive,total_certificate_prisms=prism_uses,
                blocked_interior_marker=True)


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    args = parser.parse_args()
    if args.query:
        q = json.loads(args.query.read_text())
        source,right = tuple(q['source']),set(q['right_letters'])
        rules = [(n,tuple(l),tuple(r)) for n,l,r in q['rules']]
        if any(n=='swap' or not l or not r for n,l,r in rules):
            raise ValueError('expected named rules with nonempty temporal sides')
        anchored = set(q.get('anchored',()))
        unary = private_right(rules,right,anchored)
        (a,x),(b,y) = [parse(source,rules,right,q[k]) for k in ('first','second')]
        if a!=b:
            raise ValueError('expected parallel readings')
        cert = solve(source,right,(x,y),anchored,unary)
        result = dict(raw=cert is not None,surface=cert is not None,certificate=cert)
    else:
        result = checks()
    print(json.dumps(result))
