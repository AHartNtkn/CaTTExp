"""Project every event of an unfolded positive planar diagram to its own column.

--chart FILE accepts width (initial wire count), schedule ([offset,inputs,outputs]
in one reading) and optionally judgment. A judgment is evaluated at parallel old
faces as in semistrict_surface_globular_judgment, on the same named ordinary
diagram with matching lower labels. Supply event_trees in schedule order, each
the list of private children of the event; the corresponding column is [tree].
Rows and label pairs are in the reported column order. A missing judgment just
computes the wired projection.
"""
from argparse import ArgumentParser
from fractions import Fraction
from itertools import combinations, permutations
import json
from pathlib import Path

from semistrict_surface_globular_judgment import decide, facets, tensor_rows
from semistrict_surface_planar_columns import Column
from semistrict_surface_tree_spectra import Tree


def projection(col):
    coords = {v: Fraction(v) for v in range(len(col.initial)+1)}
    spans = []
    for ins, outs in col.boxes:
        a, b = coords[col.wires[ins[0]][0]], coords[col.wires[ins[-1]][1]]
        spans.append((a,b))
        for j,w in enumerate(outs):
            coords[col.wires[w][1]] = a+(b-a)*Fraction(j+1,len(outs))

    used = set(coords.values())
    points = []
    for a,b in spans:
        x = (a+b)/2
        while x in used:
            x = (a+x)/2
        used.add(x)
        points.append(x)
    order = sorted(range(len(points)),key=points.__getitem__)
    wires = []
    for w,(a,b) in enumerate(col.wires):
        # The input schedule is one execution. Each carried event has the
        # same phase throughout the wire's lifetime (birth, consumption].
        birth = col.producer.get(w,-1)
        wires.append([(i,int(i<=birth)) for i in order if coords[a]<points[i]<coords[b]])
    return order,wires


def solve(data):
    if type(data['width']) is not int or data['width']<0:
        raise ValueError('expected a nonnegative initial wire count')
    col = Column(data['width'],data['schedule'])
    order,wires = projection(col)
    result = {'column_events':order,'wire_words':wires}
    if 'judgment' in data:
        j = data['judgment']
        if j['degree']<3 or len(j['event_trees'])!=len(order):
            raise ValueError('expected degree >= 3 and one private tree per event')
        result['raw_filler'] = decide({**j,'columns':[[j['event_trees'][i]] for i in order]})
    return result


def cuts(col):
    frontiers = {}
    edges = {}
    def walk(done,live):
        if done in frontiers:
            assert frontiers[done]==live
            return
        frontiers[done] = live
        sites = edges[done] = {}
        for i,(ins,outs) in enumerate(col.boxes):
            if ins[0] in live:
                p = live.index(ins[0])
                if live[p:p+len(ins)]==ins:
                    sites[i] = p
                    walk(done|{i},live[:p]+outs+live[p+len(ins):])
    walk(frozenset(),col.initial)
    return frontiers,edges


def checks():
    examples = [(1,[(0,1,2),(1,1,2),(0,1,1),(1,2,1),(0,2,1)]),
                (3,[(2,1,2),(0,2,1),(1,2,1),(0,1,2),(0,3,2)]),
                (3,[(2,1,2),(0,1,2),(2,1,1),(1,2,1),(2,2,1)]),
                (2,[(0,2,3),(2,1,1),(0,1,1),(1,1,1),(0,3,1)]),
                (1,[])]
    pair_count = box_count = wide = 0
    for width,schedule in examples:
        col = Column(width,schedule)
        order,wires = projection(col)
        for i,(ins,outs) in enumerate(col.boxes):
            before = sum((wires[w] for w in ins),[])
            after = sum((wires[w] for w in outs),[])
            assert (i,0) in before
            assert after==[(e,int(b or e==i)) for e,b in before]
            wide += any(len(wires[w])>1 for w in (*ins,*outs))
        frontiers,sites = cuts(col)
        for done,live in frontiers.items():
            assert sum((wires[w] for w in live),[])==[(i,int(i in done)) for i in order]
            enabled = sorted(sites[done],key=sites[done].get)
            assert enabled==sorted(enabled,key=order.index)
            box_count += 2**len(enabled)-1
        readings = {p for p in permutations(order) if all(
            p[j] in sites.get(frozenset(p[:j]),{}) for j in range(len(p)))}
        for start in readings:
            reached = {start}
            queue = [start]
            while queue:
                p = queue.pop()
                for j,(a,b) in enumerate(zip(p,p[1:])):
                    pos = sites[frozenset(p[:j])]
                    if b in pos and pos[a]>pos[b]:
                        q = p[:j]+(b,a)+p[j+2:]
                        if q not in reached:
                            reached.add(q)
                            queue.append(q)
            for goal in readings:
                assert (goal in reached)==all(start.index(a)>start.index(b)
                    or goal.index(a)<goal.index(b) for a,b in combinations(order,2))
                pair_count += 1

    # Simultaneously enabled three-event cut after a split and before a merge.
    # Exercise the actual solver with private cells at heights 2,3,2 there.
    width,schedule = examples[3]
    order,wires = projection(Column(width,schedule))
    private = [[],[[]],[[]],[[[]]],[]]
    checked = 0
    for degree in (4,5,6,7,8):
        def truncate(t,h):
            return [truncate(c,h-1) for c in t] if h else []
        arities = [truncate(t,degree-3) for t in private]
        trees = [Tree([arities[i]]) for i in order]
        for w in tensor_rows(trees,degree-1):
            fixed = dict(zip(order,w))
            if fixed[0]!=(0,1) or fixed[4]!=(0,0) or any(fixed[i][0]==0 for i in (1,2,3)):
                continue
            source,target = [],[]
            for f,sign in facets(trees,w):
                entry = [[(d,t.layers[d].index(x)) for (d,x),t in zip(f,trees)],1]
                (source if sign<0 else target).append(entry)
            slots = [(i,i) for i,t in enumerate(trees) for _ in t.layers.get(degree-2,())]
            j = dict(degree=degree,event_trees=arities,slots=slots,moves=[],
                     source=source,target=target)
            data = dict(width=width,schedule=schedule,judgment=j)
            assert solve(data)['raw_filler']
            j.update(source=target,target=source)
            assert not solve(data)['raw_filler']
            checked += 1
    assert checked and wide
    print(f'{len(examples)} diagrams, {wide} boxes with multi-event wires, {box_count} enabled '
          f'charts, {pair_count} endpoint pairs, both directions of {checked} decorated atoms')


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('--chart',type=Path)
    args = p.parse_args()
    if args.chart:
        print(json.dumps(solve(json.loads(args.chart.read_text()))))
    else:
        checks()
