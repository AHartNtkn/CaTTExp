"""Resolve changing runs of spatial endomorphisms into fixed positioned strands and project by wire representatives."""
from argparse import ArgumentParser
from collections import defaultdict, deque
from itertools import groupby
from pathlib import Path
import json

from semistrict_surface_packet_meetings import decide as scalar, supported as one_gap
from semistrict_surface_polygon_grades import network
from semistrict_surface_positioned_packets import decide as positioned
from semistrict_surface_polygon_cabling import rectangle
from semistrict_surface_signed_width_two import Movies, Presentation, Rule
from semistrict_surface_transfer_cables import wire_weights


def runs(model,face):
    def shape(step):
        off,e = step
        return (off,*model.pres.marks[e],model.pres.mark_roots[e])
    return [(key,len(tuple(group))) for key,group in groupby(face,shape)]


def supported(model,actions):
    if model.attachments:
        return False
    for rid in {n for n,_ in actions if n!='swap'}:
        r = model.pres.rules[rid]
        a,b = runs(model,r.source),runs(model,r.target)
        if len(a)!=len(b) or any(k!=l or (k[1]!=k[2] and i!=j) for (k,i),(l,j) in zip(a,b)):
            return False
    return True


def run_weights(edges,parts):
    # Start with a path cover, then lower the resolution width by augmenting
    # in the residual network down to the one-unit lower bound on each wire.
    weights = wire_weights(edges,parts,parts)
    initial,final = object(),object()
    creator = {e:p for p,(_,_,outs) in parts.items() for e in outs}
    consumer = {e:p for p,(_,ins,_) in parts.items() for e in ins}
    neighbors = defaultdict(list)
    for e in edges:
        a,b = creator.get(e,initial),consumer.get(e,final)
        neighbors[a].append((b,e,1))
        neighbors[b].append((a,e,-1))
    while True:
        parents,queue = {final:None},deque([final])
        while queue and initial not in parents:
            p = queue.popleft()
            for q,e,d in neighbors[p]:
                if q not in parents and (d>0 or weights[e]>1):
                    parents[q] = p,e,d
                    queue.append(q)
        if initial not in parents:
            return weights
        p = initial
        while p is not final:
            p,e,d = parents[p]
            weights[e] += d


def wire_labels(source,model,graph):
    labels = {(-1,i):e for i,(_,e) in enumerate(source)}
    for rid,_,outs in graph.values():
        labels.update((e,s) for e,(_,s) in zip(outs,model.pres.rules[rid].target))
    return labels


def uniform_layout(model,source,graph):
    labels = wire_labels(source,model,graph)
    parts = {}
    for p,(rid,ins,outs) in graph.items():
        r = model.pres.rules[rid]
        i,j = 0,0
        for t,((shape,x),(_,y)) in enumerate(zip(runs(model,r.source),runs(model,r.target))):
            if shape[1]==shape[2]:
                parts[p,t] = rid,ins[i:i+x],outs[j:j+y]
            i,j = i+x,j+y
    weights = run_weights(labels,parts)
    layout = {e:((0,*model.pres.marks[s],model.pres.mark_roots[s]),)*weights[e] for e,s in labels.items()}
    return layout,{e:0 for e in labels}


def valid_wire(model,label,row,selected):
    source,target = model.pres.marks[label]
    root = model.pres.mark_roots[label]
    for k,(off,s,t,vertex) in enumerate(row):
        if k==selected:
            if (off,s,t,vertex)!=(0,source,target,root):
                return False
        else:
            path = source if k<selected else target
            if s!=t or not 0<=off<=len(path) or not path.startswith(s,off):
                return False
            if (model.pres.edges[path[off-1]][1] if off else root)!=vertex:
                return False
    return True


class Resolution:
    def __init__(self,model,source,graph,layout,selected):
        self.model,self.source,self.graph = model,source,graph
        self.initial = [(-1,i) for i in range(len(source))]
        self.weights = {e:len(row) for e,row in layout.items()}
        self.units = {e:tuple(f'w{n}.{j}' for j in range(len(row))) for n,(e,row) in enumerate(layout.items())}
        self.selected = {self.units[e][j] for e,j in selected.items()}
        self.layout = layout
        self.labels = wire_labels(source,model,graph)
        ports,roots = {},{}
        for e,row in layout.items():
            for u,(_,s,t,root) in zip(self.units[e],row):
                ports[u],roots[u] = (s,t),root
        def expand(face,edges):
            return tuple((i+local,u) for (i,_),e in zip(face,edges)
                         for u,(local,_,_,_) in zip(self.units[e],layout[e]))
        rules = []
        for p in range(len(graph)):
            rid,ins,outs = graph[p]
            r = model.pres.rules[rid]
            rules.append(Rule(r.path,expand(r.source,ins),expand(r.target,outs)))
        self.base = expand(source,self.initial)
        self.unit_model = Movies(Presentation(model.pres.edges,ports,rules,roots),model.start)

    def lift(self,reading):
        wires,word = self.initial.copy(),[]
        for i,p in reading:
            off = sum(self.weights[e] for e in wires[:i])
            if p is None:
                a,b = wires[i:i+2]
                word.extend(('swap',j) for j in rectangle(off,self.weights[a],self.weights[b]))
                wires[i:i+2] = b,a
            else:
                _,ins,outs = self.graph[p]
                assert tuple(wires[i:i+len(ins)])==ins
                word.append((p,off))
                wires[i:i+len(ins)] = outs
        return word

    def project(self,actions,representatives=None):
        keep = self.selected if representatives is None else set(representatives)
        if any(len(keep.intersection(row))!=1 for row in self.units.values()):
            raise ValueError('select one unit of each macro wire')
        if representatives is not None:
            if any(not valid_wire(self.model,self.labels[e],self.layout[e],row.index(u))
                   for e,row in self.units.items() for u in row if u in keep):
                raise ValueError('the chosen unit must realize the original positioned event')
        units = [u for _,u in self.base]
        out = []
        for name,i in actions:
            j = sum(u in keep for u in units[:i])
            if name in ('swap','undo'):
                a,b = units[i:i+2]
                if a in keep and b in keep:
                    out.append((name,j))
                units[i:i+2] = b,a
            else:
                rid,ins,outs = self.graph[name]
                before = [u for e in ins for u in self.units[e]]
                assert units[i:i+len(before)]==before
                out.append((rid,j))
                units[i:i+len(before)] = [u for e in outs for u in self.units[e]]
        return out


def named_diagram(model,source,first,second):
    model.pres.walk(model.start,source)
    if model.parse(source,first)[1] != model.parse(source,second)[1]:
        raise ValueError('expected parallel readings')
    arities = [(len(r.source),len(r.target)) for r in model.pres.rules]
    ids = {}
    a,b = [network(source,w,ids,arities,'swap') for w in (first,second)]
    if a[:2]!=b[:2]:
        return None
    return a[1],a[2],b[2]


def resolve(model,source,first,second):
    if not supported(model,(*first,*second)):
        raise ValueError('expected matching positioned shapes with multiplicity changes only in spatial endomorphism runs')
    data = named_diagram(model,source,first,second)
    if data is None:
        return None
    graph,a,b = data
    res = Resolution(model,source,graph,*uniform_layout(model,source,graph))
    return res,res.lift(a),res.lift(b)


def decide(model,source,first,second,radius=None):
    data = resolve(model,source,first,second)
    if data is None:
        return dict(surface=False,obstruction='named incidence')
    res,a,b = data
    solver = scalar if one_gap(res.unit_model,res.base,(*a,*b)) else positioned
    answer = solver(res.unit_model,res.base,a,b,radius)
    return dict(surface=answer['surface'],resolved_width=len(res.base),unit_comparison=answer)


def checks():
    from itertools import product
    from semistrict_surface_component_braids import cabling
    from semistrict_surface_serial_polygons import decide as serial
    from semistrict_surface_raw_movie_graph import raw_compare

    s = ((0,'s'),)
    rules = [Rule('',s,s*2),Rule('',s*2,s),Rule('',s,s),Rule('',s,s*3)]
    model = Movies(Presentation({},{'s':('','')},rules,{'s':0}),'')
    def crossing(w):
        return [('swap',g-1) for g in w]
    def moving(tokens):
        names,sizes = list(range(4)),[1]*4
        out = []
        for x in (*tokens,1,1,1,1):
            if x>0:
                i = x-1
                a,b = names[i:i+2]
                u,v = sizes[a],sizes[b]
                off = sum(sizes[e] for e in names[:i])
                out.extend(crossing(tuple(off+g for g in cabling(((a,0,u),(b,u,u+v)),(1,)))))
                names[i:i+2] = b,a
            else:
                i = -x
                e = names[i]
                out.append((0 if e==0 else 2,sum(sizes[f] for f in names[:i])))
                if e==0:
                    sizes[e] = 2
        out.append((1,sum(sizes[e] for e in names[:names.index(0)])))
        return out
    u = moving((0,2,1,0,3,2,1,-3,3))
    v = moving((2,3,-3,1,2,3,0,-3,1))
    lifted,a,b = resolve(model,s*4,u,v)
    assert lifted.project(a)==u and lifted.project(b)==v
    assert decide(model,s*4,u,v,0)['surface'] is None
    moving_result = decide(model,s*4,u,v,4)
    assert moving_result['surface'] and model.compare(s*4,u,v)['surface']
    assert raw_compare(model,s*4,u,v)['raw']

    # Exhaust all representatives on both sides of a split. The spectator
    # will itself split three ways, so its chosen unit ranges over a full run.
    res,a,b = resolve(model,s*2,[(0,0),(3,2)],[(3,1),(0,0)])
    assert decide(model,s*2,[(0,0),(3,2)],[(3,1),(0,0)])['surface']
    rows = list(res.units.values())
    k = len(res.unit_model.pres.rules[0].source)
    q = len(res.unit_model.pres.rules[1].source)
    prisms = real = 0
    for keep in product(*rows):
        assert res.project(a,keep)==[(0,0),(3,2)] and res.project(b,keep)==[(3,1),(0,0)]
        pre = []
        for i in range(q):
            for sign in ('swap','undo'):
                leg = [(sign,j) for j in reversed(range(i,i+k))]
                left = res.project(pre+[(0,i)]+leg,keep)
                right = res.project(pre+leg+[(0,i+1)],keep)
                if left!=right:
                    assert left==[(0,0),(sign,1),(sign,0)] and right==[(sign,0),(0,1)]
                    real += 1
                prisms += 1
            pre.extend(('swap',j) for j in reversed(range(i,i+k)))

    # A chain gives an independent surface decision even on a cyclic scalar base.
    from semistrict_surface_single_polygon import expand
    cases = yes = 0
    for slot,length in product(range(3),range(4)):
        for w in product((1,2),repeat=length):
            order = list(range(3))
            for g in w:
                order[g-1:g+1] = order[g],order[g-1]
            j = order.index(slot)
            u = [(0,slot),(1,slot)]+crossing(w)
            v = crossing(w)+[(0,j),(1,j)]
            bounded = decide(model,s*3,u,v,1)
            expected = serial(model,s*3,u,v)['surface']
            assert bounded['surface'] == expected
            cases += 1
            yes += expected

    # Separate scalar gaps before and after a tangible f event. One scalar
    # contracts on the left while another duplicates on the right.
    marks = {'a':('',''),'A':('',''),'b':('',''),'B':('',''),
             'm':('f','f'),'M':('f','f'),'d':('g','g'),'e':('h','h')}
    srcface = ((0,'a'),(0,'a'),(0,'m'),(1,'b'))
    dstface = ((0,'A'),(0,'M'),(1,'B'),(1,'B'))
    planar = Movies(Presentation({'f':(0,1),'g':(1,2),'h':(2,3)},marks,
                    [Rule('f',srcface,dstface),Rule('h',((0,'e'),),((0,'e'),))],
                    {'a':0,'A':0,'b':1,'B':1}),'fgh')
    src = ((1,'d'),)+srcface+((2,'e'),)
    sw = [('swap',i) for i in range(4)]
    u = sw+[(0,0),(1,5)]
    v = [(1,5),(0,1)]+sw
    placed = decide(planar,src,u,v,2)
    assert placed['surface'] and raw_compare(planar,src,u,v)['raw']
    assert decide(planar,src,v,u,2)['surface'] is False
    # A nonempty endomorphism run may also split: the extra events act on f.
    f = ((0,'x'),)
    e = ((0,'z'),)
    endos = Movies(Presentation({'f':(0,1),'g':(1,2),'h':(2,3)},
                {'x':('f','f'),'y':('g','g'),'z':('h','h')},[Rule('f',f,f*2),Rule('h',e,e)]),'fgh')
    src = ((1,'y'),(0,'x'),(2,'z'))
    u = [('swap',0),(0,0),(1,3)]
    v = [(1,2),(0,1),('swap',0),('swap',1)]
    assert decide(endos,src,u,v,2)['surface'] and raw_compare(endos,src,u,v)['raw']
    return dict(chain_cases=cases,chain_positive=yes,projected_prisms=prisms,nonidentity_prisms=real,
                split_merge_width=moving_result['resolved_width'],
                split_merge_meeting_radius=moving_result['unit_comparison']['meeting_radius'],
                mixed_width=placed['resolved_width'],mixed_radius=placed['unit_comparison']['radius'])


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
