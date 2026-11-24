"""Compute the exact full Gray interchange failure spectrum on any planar 2-base with private higher generators.

--base FILE uses the path and declaration format of semistrict_surface_planar_layer_spectrum.
Empty sides are allowed; scalar_at maps each mark with two empty sides to its vertex.
The checks construct the integral square ideal on actual diagram cuts before
comparing its highest rank and kernel with the projected clique calculations.
"""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import combinations, product
import json
from pathlib import Path
from random import Random

from semistrict_surface_globular_judgment import facets
from semistrict_surface_planar_columns import Column
from semistrict_surface_planar_event_projection import cuts, projection
from semistrict_surface_planar_layer_spectrum import presentation, profile
from semistrict_surface_square_quotient_chains import Space
from semistrict_surface_tree_spectra import Tree, context_spectrum, cycles


def solve(data):
    slots,heights,arrows,_ = presentation(data,allow_empty=True)
    result = context_spectrum(dict(edges=arrows,slots=[(*s,heights[s]) for s in slots]))
    if 'failing_from' not in result or all(a and b for a,b in data['marks'].values()):
        return result

    # Use only real generating edges for a positive-length middle path.
    edges,marks = data['edges'],data['marks']
    scalar = data.get('scalar_at',{})
    vertices = {v for s in slots for v in s}|{v for edge in edges.values() for v in edge}
    nonempty = {v:set() for v in vertices}
    for a,b in edges.values():
        nonempty[a].add(b)
    for b in vertices:
        for a in vertices:
            if b in nonempty[a]:
                nonempty[a].update(nonempty[b])
    sites = []
    for name,(a,b) in marks.items():
        path = a or b
        sites.append((edges[path[0]][0],edges[path[-1]][1],False) if path
                     else (scalar[name],scalar[name],True))
    fails_three = any(x in nonempty[y] or (x==y and not (s and t))
                      for _,y,s in sites for x,_,t in sites)
    return {'failing_from':3 if fails_three else 4}


def subsets(seq):
    for n in range(len(seq)+1):
        yield from combinations(seq,n)


def check_shape(col, children):
    order,wires = projection(col)
    ts = [Tree([children[e]]) for e in order]
    frontier,sites = cuts(col)
    chart = {}
    for done,live in frontier.items():
        enabled = sorted(sites[done],key=sites[done].get)
        for active in subsets(enabled):
            word = tuple((0,int(i in done)) for i in order)
            chart[done,active] = word
    if not chart:
        raise AssertionError('missing initial cut')
    shapes = {a for _,a in chart}
    max_rank = max(profile([ts[order.index(e)].height for e in a]) for a in shapes)
    top = defaultdict(set)
    killed = set()
    basis = set()
    for (_,a),initial in chart.items():
        full = [((0,x),) for _,x in initial]
        for e in a:
            i = order.index(e)
            full[i] = tuple((d,x) for d,layer in ts[i].layers.items() if d for x in layer)
        for word in product(*full):
            basis.add(word)
            degrees = [d for d,_ in word if d]
            if any(i==j==1 for i,j in zip(degrees,degrees[1:])):
                killed.add(word)
                if sum(degrees)==max_rank:
                    top[a].add(word)
    # Independently concatenate stationary wires and marked private cells
    # along the spatial 1-graph, without inspecting any temporal cut.
    arrows = defaultdict(list)
    for j,(a,b) in enumerate(col.wires):
        arrows[a].append((b,tuple((0,phase) for _,phase in wires[j])))
    for e,(ins,_) in enumerate(col.boxes):
        i = order.index(e)
        start,end = col.wires[ins[0]][0],col.wires[ins[-1]][1]
        tokens = sum((wires[w] for w in ins),[])
        for d,row in ts[i].layers.items():
            if d:
                for x in row:
                    term = tuple((d,x) if j==e else (0,phase) for j,phase in tokens)
                    arrows[start].append((end,term))
    def pastes(at):
        if at==len(col.initial):
            yield ()
        for to,term in arrows[at]:
            for tail in pastes(to):
                yield term+tail
    assert basis==set(pastes(0))
    # Check the actual cellular differential throughout, before quotienting.
    assert all(f in basis for w in basis for f,_ in facets(ts,w))
    assert max((sum(d for d,_ in w) for w in killed),default=0)==max_rank
    image = Space()
    for words in top.values():
        for w in words:
            image.insert(dict(facets(ts,w)))
    nullity = sum(map(len,top.values()))-len(image.rows)
    separate = 0
    for a,words in top.items():
        assert not any(set(a)<set(b) for b in shapes)
        selected = [order.index(e) for e in a]
        outside = [i for i in range(len(order)) if i not in selected]
        assert len({tuple(w[i] for i in outside) for w in words})==1
        sub = [ts[i] for i in selected]
        projected = {tuple(w[i] for i in selected) for w in words}
        expected = {w for w in product(*[[(d,x) for d,row in t.layers.items() if d for x in row] for t in sub])
                    if sum(d for d,_ in w)==max_rank and any(p[0]==q[0]==1 for p,q in zip(w,w[1:]))}
        assert projected==expected
        separate+=cycles(sub)
    assert nullity==separate
    return len(basis),len(killed),len(top),nullity


def check_paths(col):
    frontiers,_ = cuts(col)
    def paths(at):
        if at==len(col.initial):
            yield ()
        for i,(a,b) in enumerate(col.wires):
            if a==at:
                for tail in paths(b):
                    yield (i,)+tail
    assert set(paths(0))==set(frontiers.values()) and len(frontiers)==len(set(frontiers.values()))
    return len(frontiers)


def checks():
    def private(h):
        t=[]
        for _ in range(h-1):
            t=[t]
        return t
    # Distinct maximizing triples sharing outer or middle slots, including
    # the branched private tree of the extremal degree-six certificate.
    wide = Column(1,[(0,1,3),(0,1,1),(1,1,1),(2,1,1),(1,1,1),(0,3,1)])
    branch = [[[]],[[]]]
    cases = [(wide,[[],[[]],branch,[[]],branch,[]]),
             (Column(3,[(1,1,1),(0,1,2),(3,1,1),(0,2,1)]),
              [branch,[[]],[[]],[[]]])]
    rng = Random(31)
    for _ in range(36):
        width = rng.randint(1,4)
        count = width
        schedule = []
        for j in range(5):
            a,b = rng.randint(1,min(count,3)),rng.randint(1,3)
            schedule.append((rng.randrange(count-a+1),a,b))
            count += b-a
        cases.append((Column(width,schedule),[private(rng.randint(1,4)) for _ in schedule]))
    totals = [0]*4
    frontiers = 0
    for col,shapes in cases:
        frontiers += check_paths(col)
        for j,x in enumerate(check_shape(col,shapes)):
            totals[j]+=x
    # The eight-slot gap is realized with genuinely length-changing sides and
    # the given private heights. All links are spatial edges, not extra marks.
    masks = [0,0,3,2,0,17,15,95]
    heights = [50,10,10,50,10,50,50,10]
    data = dict(edges={},marks={},higher=[{} for _ in range(max(heights)-1)])
    for i,(mask,d) in enumerate(zip(masks,heights)):
        edges = [f'{x}{i}' for x in 'abc']
        start,end = f's{i}',f't{i}'
        data['edges'].update(zip(edges,((start,end),(start,f'v{i}'),(f'v{i}',end))))
        for j in range(i):
            if mask&(1<<j):
                data['edges'][f'p{j}_{i}'] = (f't{j}',start)
        names = [f'm{i}_{d}_0',f'm{i}_{d}_1']
        for name in names:
            data['marks'][name] = [edges[:1],edges[1:]]
        for k in range(d-1):
            new = [f'u{i}_{k}_0',f'u{i}_{k}_1']
            data['higher'][k].update((name,names) for name in new)
            names = new
    assert solve(data)=={'failing_degrees':list(range(3,64))}
    data['edges']['back'] = ('t0','s0')
    assert solve(data)=={'failing_from':3}
    print(f'{len(cases)} planar diagrams, {frontiers} path/ideal bijections counted by cuts, '
          f'{totals[0]} actual basis words, {totals[1]} killed words, {totals[2]} maximizing '
          f'cliques, total highest-kernel dimension {totals[3]}; eight-slot spectrum 3–63')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--base',type=Path)
    args=p.parse_args()
    if args.base:
        print(json.dumps(solve(json.loads(args.base.read_text()))))
    else:
        checks()
