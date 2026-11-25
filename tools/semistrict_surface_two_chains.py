"""Check asphericity conditions for planar histories with batches of size at most two.

JSON input: 'events' lists uses with 'name', 'input' and 'output' gate-occurrence
IDs and 'point' (vertex of an empty spatial path, or null for a nonempty path).
Initial gate IDs need no producer. Optionally pass 'chart' with gate-forest
graph data, a diagram of individually named gates, 'first', 'second', and the
two relative port diagrams 'first_output' and 'second_input'.
"""
from argparse import ArgumentParser
from itertools import combinations, product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from relative_coherence_local_links import Circuits
from semistrict_surface_component_braids import Components
from semistrict_surface_gate_forests import Presentation, cable
from semistrict_surface_history_group import HistoryGroup
from semistrict_surface_shared_edge import braid_image


def network(events):
    names = [e['name'] for e in events]
    if len(set(names))!=len(names):
        raise ValueError('use names must be distinct')
    producers, consumers = {}, set()
    for i,e in enumerate(events):
        for g in e['output']:
            if g in producers:
                raise ValueError('a gate has two producers')
            producers[g] = i
        for g in e['input']:
            if g in consumers:
                raise ValueError('a gate has two consumers')
            consumers.add(g)
    before = [{producers[g] for g in e['input'] if g in producers} for e in events]
    for j in range(len(events)):
        for s in before:
            if j in s:
                s.update(before[j])
    if any(i in s for i,s in enumerate(before)):
        raise ValueError('cyclic gate incidence')
    def incomparable(i,j):
        return i not in before[j] and j not in before[i]
    triple = next(([names[i] for i in t] for t in combinations(range(len(events)),3)
                   if all(incomparable(i,j) for i,j in combinations(t,2))),None)
    bad = [(names[i],names[j]) for i,a in enumerate(events) for j,b in enumerate(events)
           if i!=j and incomparable(i,j) and a['point'] is not None
           and a['point']==b['point'] and not a['output'] and not b['input']]
    return dict(incomparable_triple=triple,possible_singular_splits=bad,
                aspherical_by_network=triple is None and not bad)


def audit_networks():
    # Independently compare the triple test with explicit two-chain covers.
    pairs = list(combinations(range(5),2))
    for mask in range(1<<len(pairs)):
        es = [dict(name=i,input=[],output=[],point=None) for i in range(5)]
        adj = [set() for _ in es]
        for k,(i,j) in enumerate(pairs):
            if mask & (1<<k):
                es[i]['output'].append(k)
                es[j]['input'].append(k)
                adj[i].add(j)
        reach = []
        for i in range(5):
            seen = set()
            pending = list(adj[i])
            while pending:
                j = pending.pop()
                if j not in seen:
                    seen.add(j)
                    pending.extend(adj[j])
            reach.append(seen)
        def chain(l):
            return all(j in reach[i] for i,j in zip(l,l[1:]))
        cover = any(all(chain([i for i in range(5) if bits[i]==v])
                        for v in (0,1)) for bits in product((0,1),repeat=5))
        assert network(es[::-1])['aspherical_by_network']==cover
    es = [dict(name=g,input=[],output=[],point='x') for g in 'LR']
    assert len(network(es)['possible_singular_splits'])==2
    es[0]['point'] = 'y'
    assert network(es)['aspherical_by_network']
    print('1,024 gate networks agree with direct two-chain covers')


def split_test(data):
    f,s = data['first'],data['second']
    if f==s:
        raise ValueError('expected two distinct markers')
    right,left = data['first_output'],data['second_input']
    model = Presentation(dict(data,rules={'R':[f,right],'L':[s,left]}))
    names = [g for _,g in model.diagram]
    if len(set(names))!=len(names) or f not in names or s not in names:
        raise ValueError('use individually named occurrences including both markers')
    if right or left or model.ports[f]!=('','') or model.ports[s]!=('',''):
        return True
    parts = Components(model.diagram,model.ports,len(model.path))
    return parts.face[f]!=parts.face[s]


def audit_braids():
    # In particular test two different faces of the SAME anchored component.
    fixtures = [('',[(0,'u'),(0,'v'),(0,'w')]),
                ('a',[(0,'u'),(1,'v'),(0,'w')]),
                ('',[(0,'B'),(1,'u'),(0,'D'),(0,'v'),(0,'w')]),
                ('',[(0,'B'),(1,'u'),(1,'v'),(0,'D'),(0,'w')]),
                ('',[(0,'B'),(0,'t'),(0,'D'),(0,'u'),(0,'v')])]
    ports = {'u':('',''),'v':('',''),'w':('',''),'t':('a','a'),
             'B':('','aa'),'D':('aa','')}
    words = tests = 0
    for path,rows in fixtures:
        h = tuple(rows)
        names = [g for _,g in h]
        base = dict(edges={'a':['x','x']},vertex='x',path=path,diagram=h,
                    gates={g:['x',*v] for g,v in ports.items()})
        graph = HistoryGroup(h,ports)
        # Trees give actual legal based meridians from all chart readings.
        # Include pair products to exercise cancellations in the braid group.
        basis = set(graph.braids.values())
        loops = basis | {a+b for a,b in product(basis,repeat=2)}
        n = len(rows)
        genuine = [w for w in loops if braid_image(n,w)!=braid_image(n,())]
        for a,b in combinations([g for g in names if g in 'uvwt'],2):
            for ca,cb in product((0,1),repeat=2):
                d = dict(base,first=a,second=b,
                         first_output=[(0,a)]*ca,second_input=[(0,b)]*cb)
                mono = split_test(d)
                def killed(w,g,size):
                    sizes = [size if x==g else 1 for x in names]
                    return braid_image(sum(sizes),cable(w,sizes))==braid_image(sum(sizes),())
                kernel = any(killed(w,a,ca) and killed(w,b,cb) for w in genuine)
                assert mono == (not kernel), (path,h,a,b,ca,cb)
                tests += 1
        words += len(loops)
    print(f'{tests} oriented charts checked against {words} positioned return words and products')


def tie_choices(i,j):
    # The left rule changes a unary gate on the first wire, and the right
    # rule on the last. Some require the middle wire as an idle port.
    left = 1+(i%3!=1)
    right = 1+(j%3!=2)
    c = Circuits(3,{'L':(('a',0),('b',0)),'R':(('d',right-1),('e',right-1))},
                 {g:(1,1) for g in 'abde'} | {'L':(left,left),'R':(right,right)})
    def draw(order):
        frontier = c.inputs
        marks = {}
        for g in order:
            offset,width = (0,left) if g=='L' else (3-right,right)
            marks[g] = (g,frontier[offset:offset+width])
            frontier = c.apply(g,offset,frontier)
        sides = tuple(c.expand(frontier,{marks[g]:t},(marks[k],))
                      for g,k in [('L','R'),('R','L')] for t in (0,1))
        return frontier,sides
    x,sides = draw('LR')
    y,other = draw('RL')
    assert sides==other
    return len({x,y})


def audit_links(p,q):
    # Enumerate whole cubes, then build each link from face incidences and
    # compare its simplices with all cliques in its measured one-skeleton.
    from collections import defaultdict,Counter
    links = defaultdict(set)
    cells = Counter()
    choices = {(i,j):tie_choices(i,j) for i,j in product(range(p),range(q))}
    def visit(i,j,actions):
        if (i,j)!=(p,q):
            if i<p:
                visit(i+1,j,actions+[('L',i)])
            if j<q:
                visit(i,j+1,actions+[('R',j)])
            if i<p and j<q:
                for diagram in range(choices[i,j]):
                    visit(i+1,j+1,actions+[('X',i,j,diagram)])
            return
        count = sum(a[0]=='X' for a in actions)
        cells[count] += 1
        for bits in product((0,1),repeat=count):
            vertex, germs = [],set()
            for a in actions:
                if a[0]!='X':
                    vertex.append(a[0])
                    continue
                germs.add((len(vertex),a[3]))
                vertex.extend(('LR','RL')[bits[len(germs)-1]])
            links[tuple(vertex)].add(frozenset(germs))
    visit(0,0,[])
    for simplices in links.values():
        germs = set().union(*simplices)
        for k in range(2,min(p,q)+2):
            for subset in combinations(germs,k):
                clique = all(frozenset(pair) in simplices for pair in combinations(subset,2))
                assert clique == (frozenset(subset) in simplices)
    print(f'{p} by {q} chains: {dict(sorted(cells.items()))} cubes by dimension, {len(links)} flag links')


def typed(directory):
    ctx = (STAR,STAR,arr(STAR,v(0),v(1)),arr(STAR,v(1),v(0)))
    a,b = v(2),v(3)
    u = identity(ctx,v(0))
    ab = comp2(ctx,0,a,b)
    def between(s,t):
        return arr(infer(ctx,s),s,t)
    ctx += (between(u,ab),between(ab,u),between(a,a),between(a,a))
    blank = identity(ctx,u)
    ctx += (between(v(6),v(7)),between(v(7),v(6)),between(blank,blank))
    check_ctx(ctx)
    change = comp2(ctx,2,v(8),v(9))
    lens = comp2(ctx,1,comp2(ctx,1,v(4),comp2(ctx,0,change,b)),v(5))
    pair = comp2(ctx,1,lens,v(10))
    if directory:
        out = Emitter()
        out.check_type('probeAndTwoWireChanges',ctx,pair,infer(ctx,pair))
        (directory/'TwoGateChains.agda').write_text(out.module('TwoGateChains',__doc__.splitlines()[0]))


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path,nargs='?')
    p.add_argument('--agda-dir',type=Path)
    args = p.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        result = network(data['events'])
        if 'chart' in data:
            result['chart_split_injective'] = split_test(data['chart'])
        print(json.dumps(result,indent=2))
    else:
        audit_networks()
        audit_braids()
        audit_links(3,3)
        audit_links(4,4)
        typed(args.agda_dir)
