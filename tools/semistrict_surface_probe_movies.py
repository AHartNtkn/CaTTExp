"""Locate components and collision spheres for probes beside a serial history.

Use the serial gate tracks JSON format with gate-occurrence names; no site loop
is needed. Optional probes list [gap, row, wire-gap] at the one-use input
reading for gap 0, or the preceding output reading for gaps 1 through N.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from itertools import product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_component_braids import Components, Partition
from semistrict_surface_history_group import exchange
from semistrict_surface_localized_tiers import betti_mod2
from semistrict_surface_serial_gate_tracks import read_track


class Faces:
    def __init__(self,rows,ports,width):
        self.regions = Partition()
        self.slices = []
        self.rows = tuple(rows)
        for j,(p,g) in enumerate(rows):
            self.slices.append(width)
            k,l = map(len,ports[g])
            for i in range(p+1):
                self.regions.unite((j,i),(j+1,i))
            for i in range(p+k,width+1):
                self.regions.unite((j,i),(j+1,i+l-k))
            width += l-k
        self.slices.append(width)
        self.spots = {(j,i):self.regions.at((j,i)) for j,n in enumerate(self.slices)
                      for i in range(n+1)}
        indices = {g:j for j,(_,g) in enumerate(rows)}
        if len(indices)!=len(rows):
            raise ValueError('use individually named gate occurrences')
        self.holes = Counter()
        components = Components(rows,ports,self.slices[0])
        self.children = defaultdict(dict)
        for name,core in components.skeleton.items():
            j = min(indices[g] for g in core)
            face = self.spots[j,rows[j][0]]
            self.holes[face] += 1
            self.children[face][name] = components.subtree[name]


def induced(source,target,pairs):
    mapping = {}
    for a,b in pairs:
        f,g = source.spots[a],target.spots[b]
        if mapping.setdefault(f,g)!=g:
            raise ValueError('inconsistent face correspondence')
    if set(mapping)!=set(source.spots.values()):
        raise ValueError('face has no representative on the prescribed slices')
    return mapping


def seam_map(old,word,ports,width):
    now = old
    result = {f:f for f in old.spots.values()}
    for letter in word:
        moved = Faces(exchange(now.rows,letter,ports),ports,width)
        kept = [(a,a) for a in now.spots if a[0]!=abs(letter)]
        step = induced(now,moved,kept)
        if len(set(step.values()))!=len(step):
            raise ValueError('a seam exchange must transport faces bijectively')
        result = {f:step[g] for f,g in result.items()}
        now = moved
    return now.rows,result


def event_homology(nodes,vertex_ranks,ties,columns):
    # The Mayer--Vietoris boundary sends a tie meridian to the children
    # enclosed on its two cuts. Keep a lift of each pivot to the tie basis.
    cuts = {}
    pivots = {}
    kernel = []
    event_masks = defaultdict(int)
    for i,(event,terms,links_site) in enumerate(columns):
        image = 0
        for generator in terms:
            image ^= 1<<cuts.setdefault(generator,len(cuts))
        lift = 1<<i
        if links_site:
            event_masks[event] |= lift
        while image:
            high = image.bit_length()-1
            if high not in pivots:
                pivots[high] = image,lift
                break
            vector,combination = pivots[high]
            image ^= vector
            lift ^= combination
        if not image:
            kernel.append(lift)
    # By Alexander duality the coordinate functional of a centre is either
    # zero or the evaluation at its bounded complementary component.
    islands = defaultdict(list)
    for event,mask in sorted(event_masks.items()):
        values = tuple((z&mask).bit_count()%2 for z in kernel)
        if any(values):
            islands[values].append(event)
    if len(islands)!=len(kernel):
        raise AssertionError('the event centres miss a bounded complementary component')
    first = ties-len(nodes)+1+sum(vertex_ranks[a] for a in nodes)-len(pivots)
    return dict(betti=[1,first,len(kernel)],simply_connected=first==0,
                event_groups=list(islands.values()))


def movie(data, *, with_homology=False, with_births=False):
    charts = data['charts']
    read_track(dict(data,charts=[dict(c,loop=()) for c in charts]), require_shared_gate=False)
    ports = {g:(s,t) for g,(_,s,t) in data['gates'].items()}
    width = len(data['path'])
    regions = Partition()
    gaps,vertices,edges = [],{},[]
    placements = {}
    births = []
    columns = []
    for j,c in enumerate(charts):
        rows = tuple(map(tuple,c['diagram']))
        slot = c['slot']
        p,site = rows[slot]
        joint = Faces(rows,ports,width)
        def side(block):
            side_rows = rows[:slot]+tuple((p+q,g) for q,g in block)+rows[slot+1:]
            dest = Faces(side_rows,ports,width)
            pairs = [(a,(a[0]+(len(block)-1 if a[0]>slot else 0),a[1])) for a in joint.spots]
            return dest,induced(joint,dest,pairs)
        left,m = side(c['input'])
        right,n = side(c['output'])
        left_faces = m
        if not gaps:
            gaps.append(left)
            for spot,face in left.spots.items():
                placements.setdefault((0,face),dict(kind='initial',spot=list(spot)))
        else:
            reached,forward = seam_map(gaps[-1],data['seams'][j-1],ports,width)
            assert reached==left.rows
            back = {y:x for x,y in forward.items()}
            m = {f:back[g] for f,g in m.items()}
        gaps.append(right)
        if with_births and ports[site]==('','') and not c['input'] and c['output']:
            births.append((j,m[joint.spots[slot,p]]))
        # A cut face missed by the exterior at the tie lies entirely inside
        # the written output. Record a placement there before any seam move.
        new_faces = set(right.spots.values())-set(n.values())
        if new_faces:
            local = Faces(c['output'],ports,len(ports[site][0]))
            rim = {f for (r,q),f in local.spots.items() if r in (0,len(local.rows))
                   or q in (0,local.slices[r])}
            for (r,q),f in local.spots.items():
                ambient = right.spots[slot+r,p+q]
                if ambient in new_faces and f not in rim:
                    placements.setdefault((j+1,ambient),dict(kind='output',use=j,spot=[r,q]))
            if any((j+1,f) not in placements for f in new_faces):
                raise ValueError('new cut face has no placement in the written port interior')
        for f in m:
            a,b = (j,m[f]),(j+1,n[f])
            regions.unite(a,b)
            incident_point = ports[site]==('','') and f==joint.spots[slot,p]
            if with_homology:
                for enclosed in joint.children[f].values():
                    terms = []
                    for node,cut,face,block in ((a,left,left_faces[f],c['input']),
                                                (b,right,n[f],c['output'])):
                        packet = {g for _,g in block}
                        for child in cut.children[face]:
                            if (site if child in packet else child) in enclosed:
                                terms.append((node,child))
                    columns.append((a,j,terms,site in enclosed))
            edges.append((a,joint.holes[f],incident_point and not c['input'],
                          incident_point and not c['output']))
    for j,gap in enumerate(gaps):
        for f in set(gap.spots.values()):
            vertices[j,f] = gap.holes[f]
    groups = defaultdict(list)
    for node in sorted(vertices):
        groups[regions.at(node)].append(node)
    by_root = {}
    for i,(root,nodes) in enumerate(groups.items()):
        ties = [(a[0],holes,left_loss,right_loss) for a,holes,left_loss,right_loss in edges
                if regions.at(a)==root]
        graph = not any(holes for _,holes,_,_ in ties) and not any(vertices[a] for a in nodes)
        # Grow away from a root gap. Only the newly attached cut must split
        # relative to all its incoming exterior pieces, on either sweep.
        first = max((j+1 for j,_,_,right_loss in ties if right_loss), default=nodes[0][0])
        last = min((j for j,_,left_loss,_ in ties if left_loss), default=nodes[-1][0])
        rank = (1+sum(vertices[a]-1 for a in nodes)
                +sum(1-holes for _,holes,_,_ in ties)) if first<=last else None
        section = next(placements[a] for a in nodes if a in placements)
        by_root[root] = dict(component=i,section=section,gap_faces=len(nodes),tied_faces=len(ties),
                             graph_rank=len(ties)-len(nodes)+1 if graph else None,
                             free_rank=rank,root_gaps=[first,last] if first<=last else [],
                             injective_face_maps=not any(l or r for _,_,l,r in ties),probes=0,probe_indices=[])
        if with_homology:
            local = [(j,terms,hit) for a,j,terms,hit in columns if regions.at(a)==root]
            by_root[root].update(event_homology(nodes,vertices,len(ties),local))
    for index,(gap,row,pos) in enumerate(data.get('probes',[])):
        if not 0<=gap<len(gaps) or (row,pos) not in gaps[gap].spots:
            raise ValueError('probe placement outside its gap diagram')
        group = by_root[regions.at((gap,gaps[gap].spots[row,pos]))]
        group['probe_indices'].append(index)
        group['probes'] += 1
    result = list(by_root.values())
    if with_births:
        for c in result:
            c['births'] = []
        for node in births:
            by_root[regions.at(node)]['births'].append(node[0])
    for c in result:
        c['higher_obstruction'] = ('collision sphere' if c['probes']>=2 else
            'none' if not c['probes'] or c['free_rank'] is not None or c['injective_face_maps'] else 'requires one-probe test')
        if c['probes']==1 and c.get('simply_connected'):
            c['higher_obstruction'] = 'one-probe sphere' if c['betti'][2] else 'none'
    return result


def axis_cells(m,cuts):
    # Ordered nonempty tiers of particle coordinates plus the fixed interior
    # subdivision levels. A tier can contain a level and any particles.
    orders = [tuple((-(k+1),) for k in range(cuts))]
    for i in range(m):
        new = []
        for order in orders:
            new.extend(order[:j]+((i,),)+order[j:] for j in range(len(order)+1))
            new.extend(order[:j]+(order[j]+(i,),)+order[j+1:] for j in range(len(order)))
        orders = new
    out = {}
    for o in orders:
        loc = {}
        tier = {}
        gap = 0
        for k,b in enumerate(o):
            fixed = b[0]<0
            for a in b:
                if a>=0:
                    loc[a] = 2*gap+int(fixed)
                    tier[a] = k
            gap += int(fixed)
        facets = []
        for k in range(len(o)-1):
            if o[k][0]>=0 or o[k+1][0]>=0:
                facets.append(o[:k]+(tuple(sorted(o[k]+o[k+1])),)+o[k+2:])
        out[o] = (len(o)-cuts,loc,tier,facets)
    return out


def configuration_betti(m,cuts,blocked):
    # Relative cellular chains of the compact box product modulo its
    # boundary, obstacle hits and particle diagonals. Duality gives ordinary
    # Betti numbers of the open configuration manifold in reverse degree.
    axes = [axis_cells(m,k) for k in cuts]
    cells = [[] for _ in range(3*m+1)]
    boundary = {}
    for cell in product(*axes):
        rows = [axis[o] for axis,o in zip(axes,cell)]
        if any(blocked(*(r[1][i] for r in rows)) for i in range(m)):
            continue
        if len({tuple(r[2][i] for r in rows) for i in range(m)})<m:
            continue
        cells[sum(r[0] for r in rows)].append(cell)
        boundary[cell] = {}
    for cell,facets in boundary.items():
        for i,o in enumerate(cell):
            for f in axes[i][o][3]:
                key = cell[:i]+(f,)+cell[i+1:]
                if key in boundary:
                    facets[key] = 1
    for facets in boundary.values():
        ridges = Counter(r for f in facets for r in boundary[f])
        assert not any(n%2 for n in ridges.values())
    return list(reversed(betti_mod2(cells,boundary)))


def audit():
    # A two-wire rule creates a gate on both wires, then another consumes it.
    # In the middle spatial strip the barrier spans the width during one
    # closed time interval. The two outside strips remain separate.
    rows = [(0,'H')]
    def ch(a,b):
        return dict(diagram=rows,slot=0,input=a,output=b)
    knot = [(0,'T')]
    data = dict(vertex='x',path='aa',edges={'a':['x','x']},
                gates={g:['x','aa','aa'] for g in ('H','T')},
                charts=[ch([],knot),ch(knot,[])],seams=[[]],
                probes=[[0,0,1],[1,0,1],[2,0,0]])
    got = movie(data)
    assert sorted(c['graph_rank'] for c in got)==[0,0,1]
    middle = next(c for c in got if c['graph_rank']==1)
    assert middle['higher_obstruction']=='collision sphere'
    different = movie(dict(data,probes=[[0,0,1],[1,0,0],[2,0,2]]))
    assert all(c['higher_obstruction']=='none' for c in different)
    # A separate point beside the gate crosses it by a genuine signed seam.
    sites = [dict(data['charts'][0],diagram=[(0,'H'),(2,'s')]),
             dict(data['charts'][1],diagram=[(2,'s'),(0,'H')],slot=1)]
    crossing = dict(data,gates={**data['gates'],'s':['x','','']},charts=sites,
                    seams=[[-1]],probes=data['probes'][:2])
    assert any(c['higher_obstruction']=='collision sphere' for c in movie(crossing))
    # Two scalar events at empty ports give an actual singular refinement;
    # monicity alone must leave the occupied one-probe component undecided.
    scalar = dict(vertex='x',path='',edges={},gates={'H':['x','','']},
                  charts=[dict(diagram=rows,slot=0,input=[],output=[])],
                  seams=[],probes=[[0,0,0]])
    assert movie(scalar)[0]['higher_obstruction']=='requires one-probe test'
    # Independently compute the configuration homology of the middle strip.
    # Coordinates are x across the strip, y along the drawing, t history time.
    barrier = lambda x,y,t: y==1 and 1<=t<=3
    for count,expected in [(1,[1,1,0,0]),(2,[1,2,2,1,0,0,0])]:
        actual = configuration_betti(count,[0,1,2],barrier)
        assert actual==expected
        print(f'{count} probes in the middle component: mod-two Betti numbers {actual}')
    actual = configuration_betti(3,[0,0,0],lambda *_:False)
    assert actual==[1,0,3,0,2,0,0,0,0,0]
    print('three probes in an open ball:',actual)


def typed(directory):
    ctx = (STAR,arr(STAR,v(0),v(0)))
    f = v(1)
    u = identity(ctx,v(0))
    ff = comp2(ctx,0,comp2(ctx,0,f,u),f)
    def between(s,t):
        return arr(infer(ctx,s),s,t)
    ctx += (between(ff,ff),)
    empty = identity(ctx,ff)
    node = v(2)
    blank = identity(ctx,u)
    ctx += (between(empty,node),between(node,empty),between(blank,blank))
    check_ctx(ctx)
    chain = comp2(ctx,2,v(3),v(4))
    double = comp2(ctx,1,v(5),v(5))
    middle = comp2(ctx,0,comp2(ctx,0,f,double),f)
    term = comp2(ctx,1,chain,middle)
    if directory:
        e = Emitter()
        e.check_type('twoProbesAtBridge',ctx,term,infer(ctx,term))
        (directory/'ProbeMovies.agda').write_text(e.module('ProbeMovies',__doc__.splitlines()[0]))


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('input',nargs='?',type=Path)
    p.add_argument('--agda-dir',type=Path)
    args = p.parse_args()
    if args.input:
        print(json.dumps(movie(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
        typed(args.agda_dir)
