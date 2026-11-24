"""Compare old Gray movies with two private polygon columns and arbitrary shared transfers."""
from argparse import ArgumentParser
from collections import defaultdict
from graphlib import TopologicalSorter
from itertools import product
import json
from pathlib import Path

from semistrict_surface_planar_cylinder import moves, parse
from semistrict_surface_total_ports import incidence


def cables(sides,graph,private):
    creator,consumer = {},{}
    for p in private:
        _,ins,outs = graph[p]
        creator.update((e,p) for e in outs)
        consumer.update((e,p) for e in ins)
    # Cover each edge by one complete path of the private incidence DAG.
    weight = dict.fromkeys(sides,0)
    for e in sides:
        weight[e] += 1
        back = e
        while back in creator:
            back = graph[creator[back]][1][0]
            weight[back] += 1
        ahead = e
        while ahead in consumer:
            ahead = graph[consumer[ahead]][2][0]
            weight[ahead] += 1
    units = {e:tuple((e,i) for i in range(weight[e])) for e in sides if e not in creator}
    for p in sorted(private):
        _,ins,outs = graph[p]
        row = tuple(x for e in ins for x in units[e])
        assert len(row)==sum(weight[e] for e in outs)
        i = 0
        for e in outs:
            units[e] = row[i:i+weight[e]]
            i += weight[e]
    return units


def projection(a,b,private,units,flip,lengths):
    # In the second chart reverse the execution of each 3-reading and exchange
    # the colours. Thus a right polygon is processed from its outputs to inputs.
    _,sides,graph,_ = a
    left = [e for e in sides if sides[e]==flip]
    right = [e for e in sides if sides[e]!=flip]
    observer_start = {e:p for p,side in private.items() if side!=flip
                      for e in graph[p][1 if flip else 2]}
    marker_heights,edge_heights = {},{}
    def data(diagram):
        input_words,observer_words = {},defaultdict(list)
        words = diagram[3]
        for e in left:
            fs = words.get(e,())
            fs = reversed(fs) if flip else fs
            input_words[e] = [y for f in fs for y in reversed(units[f])]
        # Origin identifiers are in causal order in the first reading.
        for f in sorted(right,reverse=bool(flip)):
            es = words.get(f,())
            for y in units[f]:
                word = observer_words[y]
                if diagram is a and f in observer_start:
                    marker_heights[observer_start[f],y] = sum(lengths.get(e,0) for e in word)
                word.extend(reversed(es) if flip else es)
        return input_words,dict(observer_words)
    current,paths = data(a)
    final,targets = data(b)
    order = TopologicalSorter()
    borders = {}
    heights = {}
    counter = 0
    def bind(e,lo,hi):
        order.add(('e',e),('gap',lo))
        order.add(('gap',hi),('e',e))
    for y,path in paths.items():
        borders[y] = list(range(counter,counter+len(path)+1))
        counter += len(path)+1
        height = 0
        heights[borders[y][0]] = height
        for j,e in enumerate(path):
            edge_heights[y,e] = height
            height += lengths.get(e,0)
            heights[borders[y][j+1]] = height
            bind(e,borders[y][j],borders[y][j+1])
    routes = {}
    for p in sorted(graph,reverse=bool(flip)):
        _,ins,outs = graph[p]
        if flip:
            ins,outs = outs,ins
        if private.get(p)!=flip:
            continue
        tail = None
        for e in ins:
            end = final[e]
            if current[e][:len(end)]!=end:
                return None
            rest = current[e][len(end):]
            if tail is not None and tail!=rest:
                return None
            tail = rest
        routes[p] = tuple(reversed(tail))
        for y in routes[p]:
            path = paths[y]
            if ins[0] not in path:
                return None
            j = path.index(ins[0])
            if tuple(path[j:j+len(ins)])!=ins:
                return None
            edge_gaps = borders[y]
            new = [edge_gaps[j],*range(counter,counter+len(outs)-1),edge_gaps[j+len(ins)]]
            counter += len(outs)-1
            for e in ins:
                assert current[e].pop()==y
                order.add(('p',p),('e',e))
            height = heights[new[0]]
            for k,e in enumerate(outs):
                edge_heights[y,e] = height
                height += lengths.get(e,0)
                if k+1==len(outs):
                    assert height==heights[new[-1]]
                heights[new[k+1]] = height
                current[e].insert(0,y)
                order.add(('e',e),('p',p))
                bind(e,new[k],new[k+1])
            path[j:j+len(ins)] = outs
            edge_gaps[j:j+len(ins)+1] = new
    if current!=final or paths!=targets:
        return None
    return {key:i for i,key in enumerate(order.static_order())},routes,edge_heights,marker_heights


def slot(whole,part):
    if part[0] not in whole:
        return None
    j = whole.index(part[0])
    return j if whole[j:j+len(part)]==part else None


def transition(words,side,p,observer,graph):
    _,ins,outs = graph[p]
    changed = words.copy()
    if side==0:
        if not all(words[e] and words[e][-1]==observer for e in ins):
            return None
        j = slot(words[observer],ins)
        if j is None:
            return None
        for e in ins:
            changed[e] = words[e][:-1]
        for e in outs:
            changed[e] = (observer,)+words[e]
        changed[observer] = words[observer][:j]+outs+words[observer][j+len(ins):]
    else:
        if not all(words[f] and words[f][0]==observer for f in outs):
            return None
        j = slot(words[observer],outs[::-1])
        if j is None:
            return None
        for f in outs:
            changed[f] = words[f][1:]
        for f in ins:
            changed[f] = words[f]+(observer,)
        changed[observer] = words[observer][:j]+ins[::-1]+words[observer][j+len(outs):]
    return changed


def bounded_counts(a,b,private,allowed):
    # If A,B are the two private incidence matrices (outputs minus inputs),
    # all square balances have the form D = A L - R B^t.
    _,sides,graph,initial = a
    final = b[3]
    wires = [[e for e in sides if sides[e]==k] for k in (0,1)]
    nodes = [sorted(p for p in private if private[p]==k) for k in (0,1)]
    producer = {e:p for p in private for e in graph[p][2]}
    consumer = {e:p for p in private for e in graph[p][1]}
    delta = {(e,f):int(f in final.get(e,()))-int(f in initial.get(e,()))
             for e in wires[0] for f in wires[1]}

    def difference(values,born,used):
        return values.get(born,0)-values.get(used,0)

    # First-input recursion is an integral left inverse to each incidence.
    left,right = {},{}
    for p in nodes[0]:
        e = graph[p][1][0]
        for f in wires[1]:
            left[p,f] = left.get((producer.get(e),f),0)-delta[e,f]
    for q in nodes[1]:
        f = graph[q][1][0]
        for e in wires[0]:
            al = difference(left,(producer.get(e),f),(consumer.get(e),f))
            right[e,q] = right.get((e,producer.get(f)),0)+delta[e,f]-al
    for (e,f),value in delta.items():
        al = difference(left,(producer.get(e),f),(consumer.get(e),f))
        rb = difference(right,(e,producer.get(f)),(e,consumer.get(f)))
        if al-rb!=value:
            return None

    # Every integral solution differs from this one by (W B^t, A W).
    # Bound each coefficient by two ordinary difference constraints.
    variables = {None:0,**{(p,q):0 for p in nodes[0] for q in nodes[1]}}
    bounds = []
    expressions = {}
    def bound(key,c,hi,lo):
        hi = hi if hi in variables else None
        lo = lo if lo in variables else None
        top = int(key in allowed)
        bounds.extend(((hi,lo,c),(lo,hi,top-c)))
        expressions[key] = c,hi,lo
    for (p,f),c in left.items():
        bound((0,p,f),c,(p,producer.get(f)),(p,consumer.get(f)))
    for (e,q),c in right.items():
        bound((1,q,e),c,(producer.get(e),q),(consumer.get(e),q))
    for _ in range(len(variables)):
        changed = False
        for u,v,d in bounds:
            upper = variables[u]+d
            if variables[v]>upper:
                variables[v] = upper
                changed = True
        if not changed:
            return variables,bounds,expressions
    return None


def describe_profiles(solution,schedule,blocked,order):
    values,bounds,expressions = solution
    def distances(reverse):
        dist = dict.fromkeys(values,float('inf'))
        dist[None] = 0
        for _ in range(len(values)-1):
            changed = False
            for src,dst,d in bounds:
                u,v = (dst,src) if reverse else (src,dst)
                if dist[u]+d<dist[v]:
                    dist[v] = dist[u]+d
                    changed = True
            if not changed:
                break
        return dist
    low = {v:-d for v,d in distances(True).items()}
    high = distances(False)
    pairs = sorted(v for v in values if v is not None and low[v]!=high[v])
    assert all(high[v]-low[v] in (0,1) for v in values)
    bits = {p:i for i,p in enumerate(pairs)}
    requires = {(bits[v],bits[u]) for u,v,d in bounds if u in bits and v in bits
                and u!=v and low[u]+d==low[v]}
    # Each variable bit contributes a signed unit to these prism counts.
    base = schedule(low)
    assert base is not None and schedule(high) is not None
    def coordinates(v,sign):
        return sorted(k for k,(_,plus,minus) in expressions.items()
                      if plus!=minus and (plus if sign>0 else minus)==v)
    return dict(minimum_schedule=base,move_order=tuple(sorted(order,key=order.__getitem__)),
                pairs=[dict(vertices=v,blocked=blocked(*v),
                            add=coordinates(v,1),subtract=coordinates(v,-1)) for v in pairs],
                requires=sorted(requires))


def compare(source,right,traces,anchored,check_schedule=None,geometry=None,profiles=False):
    ids = {}
    a,b = [incidence(source,right,path,ids) for path in traces]
    if a[:3]!=b[:3]:
        return None
    _,sides,graph,_ = a
    private = {}
    for p,(n,ins,outs) in graph.items():
        colours = {sides[e] for e in ins+outs}
        if len(colours)==1 and n not in anchored:
            private[p] = next(iter(colours))
    units = cables(sides,graph,private)
    lengths,required,exteriors,windows = geometry or ({},{},{},{})
    charts = [projection(a,b,private,units,k,lengths) for k in (0,1)]
    if any(c is None for c in charts):
        return None
    events = {}
    for side,(order,routes,_,_) in enumerate(charts):
        opposite,_,heights,starts = charts[1-side]
        for p,route in routes.items():
            if not route:
                continue
            observers = [x for e in graph[p][1] for x in units[e]]
            for f in sides:
                if sides[f]==side or ('e',f) not in opposite or slot(route,units[f]) is None:
                    continue
                if any((x,f) not in heights for x in observers):
                    continue
                if geometry and any(exteriors[p][1-side]+heights[x,f]-starts[p,x]<required[f]
                                    for x in observers):
                    continue
                pair = (order['p',p],opposite['e',f])
                events[side,p,f] = pair[::-1] if side else pair
    solution = bounded_counts(a,b,private,events)
    if solution is None:
        return None
    values,_,expressions = solution
    def schedule(values):
        selected = [key for key,(c,hi,lo) in expressions.items() if c+values[hi]-values[lo]]
        cert = tuple(sorted(selected,key=events.__getitem__))
        words = {e:tuple(a[3].get(e,())) for e in sides}
        for step in cert:
            words = transition(words,*step,graph)
            if words is None:
                return None
        if any(words[e]!=tuple(b[3].get(e,())) for e in sides):
            return None
        return cert if check_schedule is None or check_schedule(cert) else None
    cert = schedule(values)
    if not profiles or cert is None:
        return cert

    def blocked(p,q):
        if geometry is None:
            return False
        margins = []
        for side,(moving,other) in enumerate(((p,q),(q,p))):
            _,_,height,start = charts[1-side]
            wire = graph[other][1][0]
            observer = units[graph[moving][1][0]][0]
            room = exteriors[moving][1-side]+height[observer,wire]-start[moving,observer]
            margins.append(room-windows[other]-exteriors[other][1-side])
        return margins[0]<0 or margins[0]!=margins[1]
    return describe_profiles(solution,schedule,blocked,events)



def checks():
    from semistrict_surface_signed_width_two import Movies, Presentation, Rule
    from semistrict_surface_raw_movie_graph import raw_compare
    from semistrict_surface_square_mutex import diagram
    cases = [
        ('Ba',[('p','a','aa'),('q','B','BB'),('to','a','BB'),('back','B','aa')],3),
        ('Baa',[('p','aa','x'),('q','B','BB'),('g','aB','Ba')],3),
        ('BBa',[('p','a','aa'),('q','BB','X'),('g','X','a')],3),
        ('Ba',[('p','a','xx'),('q','B','XX'),('r','xx','a'),('s','XX','B'),('to','a','B')],3)]
    checked = accepted = nonempty = 0
    for s,rs,budget in cases:
        source,right = tuple(s),set('BX')
        rules = [(n,tuple(l),tuple(r)) for n,l,r in rs]
        marks = {c:(('g','g') if c in right else ('f','f')) for c in 'aBxX'}
        def history(w):
            return tuple((int(c in right),c) for c in w)
        placed = []
        for n,l,r in rules:
            which = {c in right for c in l+r}
            if len(which)==2:
                placed.append(Rule('fg',history(l),history(r)))
            else:
                placed.append(Rule('g' if True in which else 'f',tuple((0,c) for c in l),
                                   tuple((0,c) for c in r)))
        model = Movies(Presentation({'f':(0,1),'g':(1,2)},marks,placed),'fg')
        index = {n:i for i,(n,_,_) in enumerate(rules)}
        ids,groups = {},defaultdict(dict)
        todo = [(source,(),(),0)]
        while todo:
            w,trace,path,n = todo.pop()
            key = w,tuple(sorted(x for x,_ in path if x!='swap'))
            shape = diagram(source,trace,False,ids)
            if shape in groups[key]:
                continue
            groups[key][shape] = trace,path
            for name,i,l,r,out in moves(w,rules,right):
                k = n+(name!='swap')
                if k<=budget:
                    todo.append((out,trace+((name,i,l,r),),path+((index.get(name,name),i),),k))
        for group in groups.values():
            for (t,x),(u,y) in product(group.values(),repeat=2):
                cert = compare(source,right,(t,u),set())
                answer = cert is not None
                assert raw_compare(model,history(source),x,y)['raw']==answer,(s,x,y,cert)
                assert model.compare(history(source),x,y)['surface']==answer
                checked += 1
                accepted += answer
                nonempty += bool(cert)
    rules = [(n,tuple(l),tuple(r)) for n,l,r in
             [('birth','x','BBaa'),('q','BB','DDD'),('s','DDD','B'),('p','aa','ccc'),
              ('r','ccc','a'),('finish','aB','T')]]
    source,right = ('x',),set('BDT')
    before = [('birth',0),('q',0),('s',0),('swap',0),('swap',1),('p',0),('r',0),('finish',0)]
    after = [('birth',0),('p',2),('r',2),('swap',1),('swap',0),('q',1),('s',1),('finish',0)]
    traces = [parse(source,rules,right,w)[1] for w in (before,after)]
    composite = compare(source,right,traces,set())
    assert composite and compare(source,right,traces[::-1],set()) is None
    return dict(comparisons=checked,positive=accepted,nonempty_certificates=nonempty,
                transfer_split_join_prisms=len(composite))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    args = parser.parse_args()
    if args.query:
        q = json.loads(args.query.read_text())
        source,right = tuple(q['source']),set(q['right_letters'])
        rules = [(n,tuple(l),tuple(r)) for n,l,r in q['rules']]
        if any(n=='swap' or not l or not r for n,l,r in rules):
            raise ValueError('expected named rules with nonempty total sides')
        (a,x),(b,y) = [parse(source,rules,right,q[k]) for k in ('first','second')]
        if a!=b:
            raise ValueError('expected parallel readings')
        cert = compare(source,right,(x,y),set(q.get('anchored',())))
        result = dict(raw=cert is not None,surface=cert is not None,schedule=cert)
    else:
        result = checks()
    print(json.dumps(result))
