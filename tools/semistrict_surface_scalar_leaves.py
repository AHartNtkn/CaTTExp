"""Prune terminal branches and unary sites of a named scalar-rule movie.

Pass serial point-movie JSON. The returned reduced movie includes its initial
and final cut braids. For a core of through strands and isolated sites the
output also decides whether any named degree-five or degree-six obstruction
exists. An isolated site represents a free point, including after pruning.
"""
from argparse import ArgumentParser
from collections import deque
from math import comb
import json
from pathlib import Path

from semistrict_surface_component_braids import restrict
from semistrict_surface_movie_spine import expanded
from semistrict_surface_serial_gate_tracks import read_track


def swapped(order,word):
    order = list(order)
    for letter in word:
        i = abs(letter)-1
        order[i],order[i+1] = order[i+1],order[i]
    return order


def read_edges(data):
    if data['path'] or any(s or t or x!=data['vertex'] for x,s,t in data['gates'].values()):
        raise ValueError('expected a one-object point-gate movie')
    charts = data['charts']
    read_track(dict(data,charts=[dict(c,loop=()) for c in charts]),require_shared_gate=False)
    initial = list(range(len(expanded(charts[0],'input'))))
    live = initial.copy()
    sources = [None]*len(initial)
    targets = [None]*len(initial)
    steps = []
    for i,c in enumerate(charts):
        slot = c['slot']
        end = slot+len(c['input'])
        taken = live[slot:end]
        emitted = list(range(len(sources),len(sources)+len(c['output'])))
        sources.extend([i]*len(emitted))
        targets.extend([None]*len(emitted))
        for edge in taken:
            targets[edge] = i
        steps.append((live[:slot],taken,emitted,live[end:]))
        live[slot:end] = emitted
        if i<len(data['seams']):
            live = swapped(live,data['seams'][i])
    return initial,live,sources,targets,steps


def prune(data):
    initial,final,source,target,steps = read_edges(data)
    incident = [set(ins+outs) for _,ins,outs,_ in steps]
    pending = deque(i for i,edges in enumerate(incident) if len(edges)==1)
    erased = {}
    lost = set()
    while pending:
        i = pending.popleft()
        if len(incident[i])!=1:
            continue
        edge = incident[i].pop()
        other = target[edge] if source[edge]==i else source[edge]
        erased[i] = 'leaf'
        lost.add(edge)
        if other is not None:
            incident[other].remove(edge)
            if len(incident[other])==1:
                pending.append(other)

    # Label each surviving wire by the first segment of its oriented string.
    # Unary sites occur in temporal order, so its earlier label is final.
    label = list(range(len(source)))
    for i,(_,ins,outs,_) in enumerate(steps):
        if i in erased:
            continue
        a = [g for g in ins if g not in lost]
        b = [g for g in outs if g not in lost]
        if len(a)==len(b)==1:
            label[b[0]] = label[a[0]]
            erased[i] = 'unary'

    def names(edges):
        return ['w'+str(label[g]) for g in edges if g not in lost]
    def rows(labels):
        return [(0,g) for g in labels]

    charts,seams,first,last = [],[],[],[]
    isolated,essential = [],[]
    for i,(below,ins,outs,above) in enumerate(steps):
        if i not in erased:
            if charts:
                seams.append(last)
            else:
                first = last
            last = []
            site = 'site'+str(i)
            a,b = names(ins),names(outs)
            left = names(below)
            charts.append(dict(diagram=rows([*left,site,*names(above)]),slot=len(left),input=rows(a),output=rows(b)))
            (essential if a or b else isolated).append(i)
        if i<len(data['seams']):
            live = below+outs+above
            keep = {k for k,g in enumerate(live) if g not in lost}
            last.extend(restrict(len(live),data['seams'][i],keep))
    kept = set(names(range(len(source))))|{'site'+str(i) for i in isolated+essential}
    x = data['vertex']
    movie = dict(vertex=x,path='',edges={},gates={g:[x,'',''] for g in sorted(kept)},charts=charts,seams=seams)
    if charts:
        read_track(dict(movie,charts=[dict(c,loop=()) for c in charts]),require_shared_gate=False)
        assert swapped(names(initial),first)==[g for _,g in expanded(charts[0],'input')]
        assert swapped([g for _,g in expanded(charts[-1],'output')],last)==names(final)
    else:
        assert swapped(names(initial),last)==names(final)
    result = dict(initial=names(initial),final=names(final),initial_braid=first,final_braid=last,
                  movie=movie,erased_sites=erased,isolated_sites=isolated,other_sites=essential)
    if not essential:
        m,k = len(result['initial']),len(isolated)
        assert len(result['final'])==m
        result.update(through=m,free_points=k,named_degree_five_obstruction=bool(m*k),
                      degree_six_sphere_orbits=comb(k,2),all_higher_fill=k<=1)
    return result


def sample(initial,changes,seams):
    gates = {g:['x','',''] for g in initial}
    live = list(initial)
    charts = []
    for i,(slot,take,give) in enumerate(changes):
        marker = 'H'+str(i)
        new = ['g'+str(i)+'_'+str(j) for j in range(give)]
        assert 0<=slot<=len(live)-take
        orig = live[slot:slot+take]
        rows = lambda labels:[(0,g) for g in labels]
        charts.append(dict(diagram=rows(live[:slot]+[marker]+live[slot+take:]),
                           slot=slot,input=rows(orig),output=rows(new)))
        gates.update({g:['x','',''] for g in [marker,*new]})
        live[slot:slot+take] = new
        if i<len(seams):
            live = swapped(live,seams[i])
    return dict(vertex='x',edges={},path='',gates=gates,charts=charts,seams=seams)


def interval_betti(events,holes):
    """Cellular duality for vertical marked intervals with moving positions.

    Events on each interval have strictly increasing times. Distinct
    intervals on the same spatial point must have disjoint closed lives.
    A single event is already a point. Fixed holes lie on the diagonal.
    """
    from itertools import product
    from semistrict_surface_localized_tiers import betti_mod2
    from semistrict_surface_probe_movies import axis_cells

    n = len(events)
    coords = axis_cells(n,holes)
    clocks = axis_cells(sum(events),0)
    starts = [sum(events[:i]) for i in range(n)]
    dimension = 2*n+sum(events)
    cells = [[] for _ in range(dimension+1)]
    boundary = {}
    for times,(dt,_,order,_) in clocks.items():
        if any(order[j]>=order[j+1] for a,k in zip(starts,events) for j in range(a,a+k-1)):
            continue
        limits = [(order[a],order[a+k-1]) for a,k in zip(starts,events)]
        for x,y in product(coords,repeat=2):
            dx,lx,tx,_ = coords[x]
            dy,ly,ty,_ = coords[y]
            if any(lx[i]==ly[i] and lx[i]%2 for i in range(n)):
                continue
            if any(tx[i]==tx[j] and ty[i]==ty[j] and max(limits[i][0],limits[j][0])<=min(limits[i][1],limits[j][1])
                   for i in range(n) for j in range(i)):
                continue
            cell = x,y,times
            cells[dx+dy+dt].append(cell)
            boundary[cell] = {}
    for cell,faces in boundary.items():
        for i,axis in enumerate((coords,coords,clocks)):
            for part in axis[cell[i]][3]:
                face = cell[:i]+(part,)+cell[i+1:]
                if face in boundary:
                    faces[face] = 1
    return list(reversed(betti_mod2(cells,boundary)))


def classify(data):
    """Find a composite from the empty port back to itself with an event."""
    gates = set(data['point_gates'])
    if None in gates:
        raise ValueError('null denotes the empty port')
    outgoing = {g:[] for g in gates|{None}}
    for rule,(a,b) in data['rules'].items():
        if a not in outgoing or b not in outgoing:
            raise ValueError('unknown point gate on a rule')
        outgoing[a].append((rule,b))
    pending = deque([None])
    parent = {}
    while pending:
        a = pending.popleft()
        for rule,b in outgoing[a]:
            if b is None:
                witness = [rule]
                while a is not None:
                    a,name = parent[a]
                    witness.append(name)
                return dict(all_degree_six_boundaries_fill=False,closed_program=witness[::-1],
                            reflection_test='mixed scalar' if gates else 'pure scalar')
            if b not in parent:
                parent[b] = a,rule
                pending.append(b)
    return dict(all_degree_six_boundaries_fill=True,closed_program=None,reflection_test='all ten reflect')


def class_checks():
    from itertools import combinations
    # Compare with transitive closure which requires a positive-length path.
    vertices = [None,'a','b']
    edges = [(a,b) for a in vertices for b in vertices]
    total = 0
    for size in range(len(edges)+1):
        for subset in combinations(edges,size):
            reach = set(subset)
            for k in vertices:
                reach |= {(a,b) for a in vertices for b in vertices if (a,k) in reach and (k,b) in reach}
            rules = {str(i):edge for i,edge in enumerate(subset)}
            r = classify(dict(point_gates=vertices[1:],rules=rules))
            assert r['all_degree_six_boundaries_fill']==((None,None) not in reach)
            witness = r['closed_program']
            if witness:
                at = None
                for step in witness:
                    a,at2 = rules[step]
                    assert a==at
                    at = at2
                assert at is None
                # Realize two copies in one movie. Use new occurrence names
                # for their edges even if the program reuses a gate colour.
                changes = [(0,int(rules[step][0] is not None),int(rules[step][1] is not None))
                           for step in witness]*2
                r = prune(sample([],changes,[[]]*(len(changes)-1)))
                assert r['through']==0 and r['free_points']==2 and r['degree_six_sphere_orbits']==1
            total += 1
    assert classify(dict(point_gates=[],rules={'p':[None,None]}))['reflection_test']=='pure scalar'
    print(f'{total} computads agree with positive reachability; every closed-program witness replays twice')


def audit():
    from itertools import product
    from semistrict_surface_spherical_relations import analyze as spheres

    counts = 0
    def check(data):
        nonlocal counts
        r = prune(data)
        before = spheres(data)
        if not r['other_sites']:
            m,k = r['through'],r['free_points']
            # The fibre of one *additional* point sees the k finite trees as
            # k punctures. This is calculated independently from all event disks.
            assert before['betti']==[1,m,k] and before['sphere_orbits']==k
        if r['movie']['charts']:
            after = spheres(r['movie'])
            for key in ('betti','sphere_orbits'):
                assert before[key]==after[key]
        counts += 1
        return r

    # A birth supplies two branches. One terminates freely, including after
    # braiding with the through wire. The two survivors may form a cap core.
    for length in range(4):
        for word in product((1,-1,2,-2),repeat=length):
            for slot in (0,1,2):
                data = sample(['a'],[(1,0,2),(slot,1,0)],[word])
                check(data)
    # A tree with several forks/joins, two one-ended strings, one persistent
    # strand and two finite components. The last event has no incident edge.
    many = sample(['p','q'],[(1,1,0),(1,0,3),(2,1,0),(1,1,2),(1,1,0),
                             (1,1,0),(1,1,0),(1,0,1),(0,0,0)],[[]]*8)
    r = check(many)
    assert (r['through'],r['free_points'],r['degree_six_sphere_orbits'])==(1,2,1)
    # Keep a nontrivial link. Add a freely ending third daughter at birth,
    # winding the extra strand around a retained one before its death.
    for twist in ([],[1,1],[-1,-1],[1,-1]):
        d = sample(['p'],[(1,0,3),(3,1,0),(1,2,0)],[[3,3],twist])
        r = check(d)
        assert len(r['other_sites'])==2 and len(r['erased_sites'])==1
        assert spheres(d)['sphere_orbits']==int(not twist or sum(twist)==0)
    # With no event left the seam is still the actual signed through braid;
    # with a surviving event both outer cut paths may be nonempty.
    r = check(sample(['a','b'],[(0,1,1),(1,1,1)],[[1]]))
    assert r['final_braid']==[1] and r['through']==2 and not r['movie']['charts']
    r = check(sample(['a','b'],[(0,1,1),(0,0,0),(1,1,1)],[[1],[-1]]))
    assert r['initial_braid']==[1] and r['final_braid']==[-1]
    from semistrict_surface_probe_movies import configuration_betti
    for holes in (0,1,2):
        for events in ([2],[1,2],[2,2],[3,2]):
            actual = interval_betti(events,holes)
            expected = configuration_betti(len(events),[holes,holes,0],lambda x,y,t:x==y and x%2)
            assert actual==expected+[0]*(len(actual)-len(expected)),(events,holes,actual,expected)
    print('twelve marked-interval configuration spaces agree with independent point-configuration homology')
    print(f'{counts} signed histories checked against independent additional-probe spines')
    print('both Hopf signs retain their cap cycle; the mixed forest gives one deck orbit of collision spheres')


def typed(directory):
    from catt import STAR,arr,check_ctx,comp2,infer,subst_tm,subst_ty,v
    from emit_agda import Emitter
    from relative_coherence_hidden_seam import identity

    point = (STAR,)
    u = identity(point,v(0))
    scalar = arr(infer(point,u),u,u)
    blank = identity(point,u)
    ctx = point+(scalar,scalar)
    sibling,leaf = v(1),v(2)
    pair = comp2(ctx,1,sibling,leaf)
    ctx += (arr(scalar,blank,pair),arr(scalar,leaf,blank))
    check_ctx(ctx)
    placed = comp2(ctx,2,v(3),comp2(ctx,1,sibling,v(4)))
    target = point+(scalar,)
    images = [v(0),v(1),blank]
    target += (subst_ty(ctx[3],images),)
    images.extend([v(2),identity(target,blank)])
    check_ctx(target)
    for i,t in enumerate(images):
        assert infer(target,t)==subst_ty(ctx[i],images[:i])
    restore = [v(0),sibling,placed]
    for i,t in enumerate(restore):
        assert infer(ctx,t)==subst_ty(target[i],restore[:i])
    erased = subst_tm(placed,images)
    assert infer(target,erased)==target[2]
    if directory:
        emitter = Emitter()
        emitter.check_type('parentWithCapOnSecondOutput',ctx,placed,subst_ty(target[2],restore))
        emitter.check_type('erasedLeafAtWrittenEnds',target,erased,target[2])
        (directory/'ScalarLeaves.agda').write_text(emitter.module('ScalarLeaves',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        print(json.dumps(classify(data) if 'point_gates' in data else prune(data),indent=2))
    else:
        audit()
        class_checks()
        typed(args.agda_dir)
