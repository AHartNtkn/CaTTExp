"""Read weighted gap traces with arbitrary simultaneous planar sites.

Use gate-forest graph and weight fields, 'batches' with 'diagram' and a
nonempty 'sites' map from globally named markers to {input,output}, signed
'seams' and 'probes' at the coarse gaps. Optional 'orders' chooses a serial
refinement of each batch. Port and ordinary gate names identify occurrences.
"""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import combinations, permutations, product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, maximal_vars, sub_from, subst_tm, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, steps, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_birth_death_packets import expand, follow
from semistrict_surface_chain_probe import transport
from semistrict_surface_component_braids import Partition
from semistrict_surface_gap_trace import trace_faces
from semistrict_surface_gate_forests import Presentation
from semistrict_surface_history_group import inv
from semistrict_surface_localized_tiers import betti_mod2
from semistrict_surface_probe_movies import Faces, axis_cells, induced, seam_map
from semistrict_surface_serial_gate_tracks import push
from semistrict_surface_shared_edge import braid_image


def packets(batch,side):
    return {site:io[side] for site,io in batch['sites'].items()}


def validate(data):
    batches,seams = data['batches'],data['seams']
    if not batches or len(seams)+1!=len(batches):
        raise ValueError('expected one seam between consecutive batches')
    markers = [g for b in batches for g in b['sites']]
    if len(set(markers))!=len(markers):
        raise ValueError('give each site occurrence a distinct marker name')
    last = None
    for i,b in enumerate(batches):
        rows = b['diagram']
        rules = {(g,side):(g,io[side]) for g,io in b['sites'].items()
                 for side in ('input','output')}
        model = Presentation(dict(data,diagram=rows,rules=rules))
        names = [g for _,g in rows]
        if not b['sites'] or len(set(names))!=len(rows) or set(names)&set(markers)!=set(b['sites']):
            raise ValueError('each active site occurs exactly once in its batch')
        for side in ('input','output'):
            expanded = expand(rows,packets(b,side))
            labels = [g for _,g in expanded]
            if len(set(labels))!=len(labels) or set(labels)&set(markers):
                raise ValueError('use distinct gate occurrences separate from site names')
            if side=='input' and last is not None and follow(last,seams[i-1],model.ports)!=expanded:
                raise ValueError('positioned seam misses the next input')
            if side=='output':
                last = expanded


def serial_faces(data,orders):
    charts,names = [],[]
    gap_index = [0]
    if len(orders)!=len(data['batches']):
        raise ValueError('expected one order per batch')
    for batch,order in zip(data['batches'],orders):
        sites = batch['sites']
        if sorted(order)!=sorted(sites):
            raise ValueError('batch order must be a permutation of its sites')
        replacements = packets(batch,'input')
        for g in order:
            del replacements[g]
            rows = expand(batch['diagram'],replacements)
            slot = next(j for j,(_,site) in enumerate(rows) if site==g)
            charts.append(dict(diagram=rows,slot=slot,**sites[g]))
            names.append(g)
            replacements[g] = sites[g]['output']
        gap_index.append(len(charts))
    probes = []
    for i,r,p in data.get('probes',[]):
        if not 0<=i<len(gap_index):
            raise ValueError('probe outside the batch gaps')
        probes.append((gap_index[i],r,p))
    return trace_faces(dict(data,charts=charts,probes=probes),use_names=names)


def coarse(data):
    # Compute the actual span of planar faces for simultaneous batches, without
    # imposing any temporal order on their markers.
    ports = {g:(s,t) for g,(_,s,t) in data['gates'].items()}
    width = len(data['path'])
    nodes = Partition()
    gaps,edges = [],[]
    for i,b in enumerate(data['batches']):
        joint = Faces(b['diagram'],ports,width)
        def side(s):
            repl = packets(b,s)
            target = Faces(expand(b['diagram'],repl),ports,width)
            where = [0]
            for _,g in b['diagram']:
                where.append(where[-1]+(len(repl[g]) if g in repl else 1))
            return target,induced(joint,target,[(p,(where[p[0]],p[1])) for p in joint.spots])
        left,m = side('input')
        right,n = side('output')
        if gaps:
            reached,move = seam_map(gaps[-1],data['seams'][i-1],ports,width)
            assert reached==left.rows
            back = {f:e for e,f in move.items()}
            m = {f:back[a] for f,a in m.items()}
        else:
            gaps.append(left)
        gaps.append(right)
        for f in m:
            a,b = (i,m[f]),(i+1,n[f])
            nodes.unite(a,b)
            edges.append(a)
    components = defaultdict(lambda:[0,0])
    for i,gap in enumerate(gaps):
        for f in set(gap.spots.values()):
            components[nodes.at((i,f))][0] += 1
    for a in edges:
        components[nodes.at(a)][1] += 1
    return {c:e-v+1 for c,(v,e) in components.items()},gaps,nodes


def example(parts):
    blocks = [list('ab'),list('c'),list('de')]
    gates = {g:['x','aa','aa'] for g in 'ABCDEFabcde'}
    gates['z'] = ['x','a','a']
    def batch(sites,ios,offset):
        diagram = [(0,g) for g in sites]
        diagram.insert(offset,(2,'z'))
        return dict(diagram=diagram,sites={g:dict(input=[(0,k) for k in a],
                              output=[(0,k) for k in b]) for g,(a,b) in zip(sites,ios)})
    b = batch('ABC',[((),block) for block in blocks],0)
    d = batch('DEF',[(s,()) for s in parts],3)
    return dict(vertex='x',path='aaa',edges={'a':['x','x']},gates=gates,batches=[b,d],
                seams=[list(range(1,6))])


def audit():
    serials = placements = 0
    for i,j in combinations(range(1,5),2):
        data = example(['abcde'[:i],'abcde'[i:j],'abcde'[j:]])
        validate(data)
        rank,gaps,nodes = coarse(data)
        # One test point for every distinct coarse gap face.
        chosen = []
        for k,gap in enumerate(gaps):
            first = {}
            for spot,f in gap.spots.items():
                first.setdefault(f,spot)
            chosen.extend((k,*p) for p in first.values())
        references = {}
        for orders in product(permutations('ABC'),permutations('DEF')):
            partition = defaultdict(set)
            for k,r,p in chosen:
                f = nodes.at((k,gaps[k].spots[r,p]))
                entry, = serial_faces(dict(data,probes=[(k,r,p)]),orders)
                assert len(entry['interval_uses'])==rank[f]
                intervals = tuple(entry['interval_uses'])
                assert references.setdefault(f,intervals)==intervals
                partition[f].add((entry['weighted_gap'],tuple(entry['trace_face'])))
                placements += 1
            assert all(len(entries)==1 for entries in partition.values())
            assert len(set.union(*partition.values()))==len(rank)
            serials += 1
    print(f'{serials} serial refinements compared with simultaneous face maps at {placements} placements')
    # Lifts of a split temporal block are coordinate-order cells with free
    # probe times. Check their compact-support homology directly.
    orders = 0
    for m,b in product(range(1,4),repeat=2):
        axis = axis_cells(m,b)
        levels = [[] for _ in range(m+1)]
        boundary = {}
        for c,(d,_,_,facets) in axis.items():
            levels[d].append(c)
            boundary[c] = {f:1 for f in facets}
        assert betti_mod2(levels,boundary)==(0,)*m+(1,)
        orders += len(axis)
    print(f'{orders} temporal lift cells checked across nine splits')
    # Full twist of two simultaneously possible interval sites acts on probe
    # meridians in their height-time plane, even with identical endpoints.
    frame = [(1,),(2,)]
    w = (1,1)
    full = (2,2)
    changed = transport(frame,w)
    for i,image in enumerate(changed):
        assert braid_image(3,full+push((i+1,))+inv(full))==braid_image(3,push(image))
    assert changed!=frame
    print('full twist acts on the two probe meridians by',changed)


def typed(directory):
    ctx = (STAR,arr(STAR,v(0),v(0)))
    path = comp2(ctx,0,v(1),v(1))
    def between(s,t):
        return arr(infer(ctx,s),s,t)
    ctx += (between(path,path),between(path,path))
    double = comp2(ctx,1,v(2),v(2))
    empty = identity(ctx,path)
    ctx += (between(empty,double),between(v(3),empty))
    check_ctx(ctx)
    generic = tree_ctx(string_tree(1,[3,3]))
    slots = maximal_vars(generic)
    routes = [composite(generic,2,steps(generic,list(map(v,slots)),order))
              for order in ((0,1),(1,0))]
    fold = sub_from(generic,ctx,dict(zip(slots,(v(4),v(5)))))
    track = subst_tm(head(generic,*routes),fold)
    ty = between(*(subst_tm(r,fold) for r in routes))
    assert infer(ctx,track)==ty
    if directory:
        out = Emitter()
        out.check_type('sameWireBatchRefinements',ctx,track,ty)
        (directory/'BatchTraces.agda').write_text(out.module('BatchTraces',__doc__.splitlines()[0]))


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('input',nargs='?',type=Path)
    p.add_argument('--agda-dir',type=Path)
    args = p.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        validate(data)
        print(json.dumps(serial_faces(data,data.get('orders',[list(b['sites']) for b in data['batches']])),indent=2))
    else:
        audit()
        typed(args.agda_dir)
