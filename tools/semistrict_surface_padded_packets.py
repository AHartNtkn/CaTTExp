"""Find finite positioned resolutions by padding each live wire with erasable spatial events."""
from argparse import ArgumentParser
from itertools import combinations, product
from pathlib import Path
import json

from semistrict_surface_endomorphism_runs import Resolution, named_diagram, run_weights, valid_wire, wire_labels
from semistrict_surface_positioned_packets import decide as positioned
from semistrict_surface_signed_width_two import Movies, Presentation, Rule


def divisions(n,k):
    if k==0:
        if n==0:
            yield ()
        return
    for cuts in combinations(range(1,n),k-1):
        ends = (0,)+cuts+(n,)
        if n>=k:
            yield tuple(b-a for a,b in zip(ends,ends[1:]))


def flows(initial,graph,n):
    nodes = list(graph.values())
    def extend(k,weights):
        if k==len(nodes):
            yield weights
            return
        _,ins,outs = nodes[k]
        for sizes in divisions(sum(weights[e] for e in ins),len(outs)):
            yield from extend(k+1,dict(weights)|dict(zip(outs,sizes)))
    for sizes in divisions(n,len(initial)):
        yield from extend(0,dict(zip(initial,sizes)))


def paths(model,initial,graph,weights):
    # Each transported unit has one initial name and one shift in spatial
    # coordinates. Its local offset at any visit is its initial offset + shift.
    visits = {}
    name = 0
    for e in initial:
        visits[e] = [(i,0) for i in range(name,name+weights[e])]
        name += weights[e]
    for rid,ins,outs in graph.values():
        r = model.pres.rules[rid]
        row = iter((u,d+i) for e,(i,_) in zip(ins,r.source) for u,d in visits[e])
        for e,(j,_) in zip(outs,r.target):
            slots = []
            for _ in range(weights[e]):
                u,d = next(row)
                slots.append((u,d-j))
            visits[e] = slots
    return visits


def anchors(model,labels,visits,n):
    keys = list(labels)
    def local(e):
        s = labels[e]
        return *model.pres.marks[s],model.pres.mark_roots[s]
    for choice in product(*(range(len(visits[e])) for e in keys)):
        selected = dict(zip(keys,choice))
        geometry = {}
        for e,j in selected.items():
            u,d = visits[e][j]
            value = (-d,*local(e))
            if geometry.setdefault(u,value)!=value:
                break
        else:
            if len(geometry)!=n:
                continue
            layout = {}
            for e in keys:
                row = tuple((geometry[u][0]+d,*geometry[u][1:]) for u,d in visits[e])
                if not valid_wire(model,labels[e],row,selected[e]):
                    break
                layout[e] = row
            else:
                return layout,selected
    return None


def find(model,source,graph):
    initial = [(-1,i) for i in range(len(source))]
    labels = wire_labels(source,model,graph)
    # Erasing all spatial endomorphisms from an expanded face preserves the
    # ordered positioned list of genuine spatial changes of the original face.
    def changes(face):
        return [(i,s,t,model.pres.mark_roots[e]) for i,e in face
                for s,t in (model.pres.marks[e],) if s!=t]
    if any(changes(r.source)!=changes(r.target) for r in (model.pres.rules[rid] for rid,_,_ in graph.values())):
        return None
    minimum = run_weights(labels,graph)
    for n in range(sum(minimum[e] for e in initial),len(labels)+1):
        for weights in flows(initial,graph,n):
            visits = paths(model,initial,graph,weights)
            result = anchors(model,labels,visits,n)
            if result is not None:
                return Resolution(model,source,graph,*result)
    return None


def decide(model,source,first,second,radius=None):
    if model.attachments:
        raise ValueError('expected a 3-computad')
    data = named_diagram(model,source,first,second)
    if data is None:
        return dict(surface=False,obstruction='named incidence')
    graph,a,b = data
    resolution = find(model,source,graph)
    if resolution is None:
        return dict(surface=None,reason='no aligned padding by spatial endomorphisms')
    u,v = resolution.lift(a),resolution.lift(b)
    answer = positioned(resolution.unit_model,resolution.base,u,v,radius)
    return dict(surface=answer['surface'],resolved_width=len(resolution.base),unit_comparison=answer)


def checks():
    from collections import deque
    from semistrict_surface_endomorphism_runs import supported
    from semistrict_surface_raw_movie_graph import raw_compare
    from semistrict_surface_single_polygon import expand
    a,b,wide = ((0,'a'),),((1,'b'),),((0,'W'),)
    rules = [Rule('fg',a+b+wide,wide),Rule('fg',wide,b+a+wide)]
    planar = Movies(Presentation({'f':(0,1),'g':(1,2)}, {'a':('f','f'),'b':('g','g'),'W':('fg','fg')},rules),'fg')
    def layout(model,source,actions):
        graph,_,_ = named_diagram(model,source,actions,actions)
        return find(model,source,graph)
    assert layout(planar,a+b+wide,[(0,0)]) is not None
    assert layout(planar,wide,[(1,0)]) is not None
    assert layout(planar,a+b+wide,[(0,0),(1,0)]) is None
    # The opposite forced prefix orders on the shared W cannot be synchronized.
    compatible = Movies(Presentation(planar.pres.edges,planar.pres.marks,
                       [rules[0],Rule('fg',wide,a+b+wide)]),'fg')
    pad = layout(compatible,a+b+wide,[(0,0),(1,0)])
    assert pad is not None and len(pad.base)==3
    assert not supported(compatible,[(0,0),(1,0)])

    def one_face_automaton(model,left,right):
        def geometry(face):
            return [(i,*model.pres.marks[e],model.pres.mark_roots[e]) for i,e in face]
        a,b = geometry(left),geometry(right)
        def choices(row,k,letter):
            if k==2*len(row):
                return []
            off,s,t,v = row[k//2]
            i,x,y,root = letter
            dest = []
            if k%2==0 and row[k//2]==letter:
                dest.append(k+1)
            path = t if k%2 else s
            j = i-off
            if (x==y and 0<=j<=len(path) and path.startswith(x,j) and
                    (model.pres.edges[path[j-1]][1] if j else v)==root):
                dest.append(k)
            return dest
        todo,seen = deque([(0,0)]),{(0,0)}
        while todo:
            j,k = todo.popleft()
            if (j,k)==(2*len(a),2*len(b)):
                return True
            nxt = []
            if j%2: nxt.append((j+1,k))
            if k%2: nxt.append((j,k+1))
            for letter in set(a+b):
                nxt.extend(product(choices(a,j,letter),choices(b,k,letter)))
            for state in nxt:
                if state not in seen:
                    seen.add(state)
                    todo.append(state)
        return False
    rows = [r for k in (1,2) for r in product((a[0],b[0],wide[0]),repeat=k)]
    pairs = successes = 0
    for left,right in product(rows,repeat=2):
        test = Movies(Presentation(planar.pres.edges,planar.pres.marks,[Rule('fg',left,right)]),'fg')
        expected = one_face_automaton(test,left,right)
        assert (layout(test,left,[(0,0)]) is not None)==expected
        pairs += 1
        successes += expected

    # The target birth gains an erasable positioned event on its output f.
    unit = ((0,'a'),)
    born = ((0,'u'),(0,'x'))
    marks = {'a':('',''),'b':('',''),'u':('','f'),'v':('','f'),'x':('f','f')}
    rules = [Rule('',unit*2,((0,'b'),)*2),Rule('',born,((0,'v'),))]
    model = Movies(Presentation({'f':(0,0)},marks,rules,{'a':0,'b':0}),'')
    source = unit*4+born
    def swaps(w):
        return [('swap',g-1) for g in w]
    u = [(0,0),(1,4)]+swaps(expand(4,0,2,(2,1,2,3,1,1)))
    v = [(1,4)]+swaps(expand(4,0,2,(1,2,1,3)))+[(0,3)]+swaps(expand(4,3,2,(1,1)))
    assert not supported(model,u+v)
    graph,s,t = named_diagram(model,source,u,v)
    res = find(model,source,graph)
    assert res is not None and res.project(res.lift(s))==u and res.project(res.lift(t))==v
    result = decide(model,source,u,v,6)
    assert result['surface'] and not raw_compare(model,source,u,v)['raw'],result
    assert decide(model,source,v,u,1)['surface'] is False
    assert model.compare(source,u,v)['surface']
    return dict(automaton_queries=pairs,admitted=successes,shared_incompatible=True,shared_compatible_width=len(pad.base),
                birth_width=len(res.base),birth_radius=result['unit_comparison']['radius'],
                birth_raw=False)


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    parser.add_argument('--radius',type=int)
    args = parser.parse_args()
    if args.query:
        q = json.loads(args.query.read_text())
        if q.get('attachments'):
            raise ValueError('expected a 3-computad')
        rules = [Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        model = Movies(Presentation(q['edges'],q['marks'],rules,q.get('mark_roots')),q['start'])
        source = tuple(map(tuple,q['source']))
        model.pres.walk(model.start,source,q.get('vertex'))
        result = decide(model,source,q['first'],q['second'],args.radius)
    else:
        result = checks()
    print(json.dumps(result))
