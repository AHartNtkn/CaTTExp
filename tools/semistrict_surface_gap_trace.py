"""Read a probe face as a planar diagram across history time at a weighted gap.

Accepts serial gate tracks JSON (seams and charts) plus positive integer edge
weights, defaulting to one, and probes [time gap, row, actual wire gap].
All planar gates have positive conserved weight. Output includes the rule
occurrences that suffice as punctures of each occupied probe face.
"""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import accumulate, product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, subst_tm, subst_ty, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_component_braids import Components
from semistrict_surface_probe_movies import Faces, movie
from semistrict_surface_serial_gate_tracks import read_track


def analyse(data):
    charts = data['charts']
    read_track(dict(data,charts=[dict(c,loop=()) for c in charts]))
    weights = data.get('weights',{g:1 for g in data['edges']})
    if set(weights)!=set(data['edges']) or any(type(v) is not int or v<=0 for v in weights.values()):
        raise ValueError('each edge needs a positive integer weight')
    def width(word):
        return sum(weights[g] for g in word)
    for _,s,t in data['gates'].values():
        if not width(s) or width(s)!=width(t):
            raise ValueError('expected positive conserved width at each ordinary gate and chain site')
    def sweep(rows):
        path = data['path']
        positions,spans = [],[]
        for p,g in rows:
            coords = tuple(accumulate((weights[c] for c in path),initial=0))
            positions.append(coords)
            _,s,t = data['gates'][g]
            spans.append((coords[p],coords[p+len(s)],g))
            path = path[:p]+t+path[p+len(s):]
        positions.append(tuple(accumulate((weights[c] for c in path),initial=0)))
        return positions,spans
    def inserted(chart,block):
        rows,slot = chart['diagram'],chart['slot']
        p = rows[slot][0]
        return list(rows[:slot])+[(p+x,g) for x,g in block]+list(rows[slot+1:])
    slices = [sweep(inserted(charts[0],charts[0]['input']))]
    cuts = []
    for c in charts:
        cuts.append((sweep(c['diagram'])[1],sweep(inserted(c,c['input']))[1],c))
        slices.append(sweep(inserted(c,c['output'])))
    requests = defaultdict(list)
    for i,row,p in data.get('probes',[]):
        if not (0<=i<len(slices) and 0<=row<len(slices[i][0]) and 0<=p<len(slices[i][0][row])):
            raise ValueError('probe is outside the original diagram')
        requests[slices[i][0][row][p]].append((i,row))
    result = []
    for gap,points in sorted(requests.items()):
        def crosses(span):
            return span[0]<gap<span[1]
        names = [g for x,y,g in slices[0][1] if x<gap<y]
        initial = len(names)
        trace,ports,times = [],{},[0]
        for i,(site_rows,in_rows,c) in enumerate(cuts):
            assert names==[g for x,y,g in in_rows if x<gap<y]
            slot = c['slot']
            if crosses(site_rows[slot]):
                before = sum(map(crosses,site_rows[:slot]))
                m = sum(map(crosses,in_rows[slot:slot+len(c['input'])]))
                outs = [g for x,y,g in slices[i+1][1][slot:slot+len(c['output'])] if x<gap<y]
                ports[i] = ('a'*m,'a'*len(outs))
                trace.append((before,i))
                names[before:before+m] = outs
            assert names==[g for x,y,g in slices[i+1][1] if x<gap<y]
            times.append(len(trace))
        diagram = Faces(trace,ports,initial)
        cores = Components(trace,ports,initial)
        reps = defaultdict(list)
        for use,core in cores.skeleton.items():
            j = next(k for k,(_,g) in enumerate(trace) if g in core)
            reps[diagram.spots[j,trace[j][0]]].append(use)
        allocations = defaultdict(int)
        for i,row in points:
            position = sum(map(crosses,slices[i][1][:row]))
            allocations[diagram.spots[times[i],position]] += 1
        for f,count in sorted(allocations.items()):
            result.append(dict(weighted_gap=gap,trace_face=f,probes=count,
                               interval_uses=sorted(reps[f])))
    return result


def controlled(actions):
    # A unary gate on the third lane passes between every consecutive use.
    # The first two lanes exhibit the requested rotated planar trace.
    gates = {'H':['x','aaa','aaa'],'T':['x','a','a']}
    live,charts,seams = [],[],[]
    for i,(at,m,n) in enumerate(actions):
        site = [(0,g) for g in live[:at]]+[(0,'H')]+[(0,g) for g in live[at+m:]]
        born = [f'g{i}/{k}' for k in range(n)]
        for g in born:
            gates[g] = ['x','aa','aa']
        ios = [[(2,'T')]+[(0,g) for g in names] for names in (live[at:at+m],born)]
        charts.append(dict(slot=at,diagram=site,input=ios[0],output=ios[1]))
        if i:
            # From previous output to the next input slide just the control
            # gate at its legal sign past the indicated two-lane bars.
            seam = (list(range(previous+1,at+1)) if previous<at else
                    list(range(-previous,-at)))
            seams.append(seam)
        previous = at
        live[at:at+m] = born
    return dict(edges={'a':['x','x']},path='aaa',vertex='x',gates=gates,charts=charts,seams=seams)


def audit():
    choices = [(0,0,2),(1,0,0),(0,2,0),(0,0,0),(0,0,1),(0,1,0)]
    data = controlled(choices)
    # All true gaps and heights on every gap diagram, even when a single
    # physical gap has several bounded faces over the same time.
    def compare(data):
        cuts = [data['charts'][0],*data['charts']]
        probes = []
        for i,c in enumerate(cuts):
            block = c['output'] if i else c['input']
            p = c['diagram'][c['slot']][0]
            rows = c['diagram'][:c['slot']]+[(p+q,g) for q,g in block]+c['diagram'][c['slot']+1:]
            path = data['path']
            for j in range(len(rows)+1):
                probes.extend([i,j,k] for k in range(len(path)+1))
                if j<len(rows):
                    p,g = rows[j]
                    _,s,t = data['gates'][g]
                    path = path[:p]+t+path[p+len(s):]
        tests = dict(data,probes=probes)
        a,b = analyse(tests),movie(tests)
        assert sorted((len(c['interval_uses']),c['probes']) for c in a)==sorted(
            (c['graph_rank'],c['probes']) for c in b)
        bijection = {}
        for point in probes:
            query = dict(data,probes=[point])
            original = next(c for c in movie(query) if c['probes'])
            trace, = analyse(query)
            name = trace['weighted_gap'],trace['trace_face']
            assert bijection.setdefault(name,original['component'])==original['component']
            assert len(trace['interval_uses'])==original['graph_rank']
        assert len(bijection)==len(set(bijection.values()))==len(b)
        return len(probes),a
    points,classes = compare(data)
    assert any(len(c['interval_uses'])>=2 for c in classes)
    print(f'controlled split, inner point, merge and two exterior islands: {points} placements, {len(classes)} occupied faces')
    # Weight two on h: the middle gap is unavailable inside an h wire,
    # opens between two actual a wires and closes at the opposite gate.
    split = dict(vertex='x',edges={'a':['x','x'],'h':['x','x']},path='h',
                 weights={'h':2,'a':1},gates={'S':['x','h','aa'],'M':['x','aa','h'],
                     'H':['x','h','h'],'T':['x','h','h']},seams=[[]])
    def ch(left,right):
        return dict(diagram=[(0,'H')],slot=0,input=[(0,g) for g in left],
                    output=[(0,g) for g in right])
    split['charts'] = [ch('T','SM'),ch('SM','T')]
    n,faces = compare(split)
    middle = [c for c in faces if c['weighted_gap']==1]
    assert len(middle)==1 and not middle[0]['interval_uses']
    print(f'unequal spatial arities with weights 2 = 1+1: {n} actual placements, {len(middle)} accessible middle face')
    families = 0
    for m,n in product(range(1,4),repeat=2):
        family = controlled([(0,0,m),(m,0,n),(0,m,0),(0,n,0)])
        compare(family)
        families += 1
    print(f'{families} further compound traces agree with direct planar face gluing')


def typed(directory):
    ctx = (STAR,arr(STAR,v(0),v(0)),arr(STAR,v(0),v(0)))
    a,h = v(1),v(2)
    aa = comp2(ctx,0,a,a)
    def between(s,t):
        return arr(infer(ctx,s),s,t)
    ctx += (between(h,aa),between(aa,h),between(h,h))
    change = comp2(ctx,1,v(3),v(4))
    ctx += (between(v(5),change),between(change,v(5)))
    check_ctx(ctx)
    tm = comp2(ctx,2,v(6),v(7))
    flat = (STAR,arr(STAR,v(0),v(0)))
    word = comp2(flat,0,v(1),v(1))
    neutral = identity(flat,word)
    images = [v(0),v(1),word,neutral,neutral,neutral]
    # Use a fitted interval event in each direction. The two-gate port
    # retains its original writing even after its two gates map to units.
    def hom(s,t):
        return arr(infer(flat,s),s,t)
    flat += (hom(neutral,neutral),)
    # On the generic 1-disc the two identity writings compare; specialize it to ee.
    line = (STAR,STAR,arr(STAR,v(0),v(1)))
    u = identity(line,v(2))
    uu = comp2(line,1,u,u)
    label = [v(0),v(0),word]
    into = subst_tm(head(line,u,uu),label)
    back = subst_tm(head(line,uu,u),label)
    images.extend([comp2(flat,2,v(2),into),comp2(flat,2,back,v(2))])
    for i,ty in enumerate(ctx):
        assert infer(flat,images[i])==subst_ty(ty,images[:i])
    image = subst_tm(tm,images)
    goal = subst_ty(infer(ctx,tm),images)
    assert infer(flat,image)==goal
    if directory:
        out = Emitter()
        out.check_type('weightedReturn',ctx,tm,infer(ctx,tm))
        out.check_type('twoRetainedIntervals',flat,image,goal)
        (directory/'GapTrace.agda').write_text(out.module('GapTrace',__doc__.splitlines()[0]))


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path,nargs='?')
    p.add_argument('--agda-dir',type=Path)
    args = p.parse_args()
    if args.input:
        print(json.dumps(analyse(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
        typed(args.agda_dir)
