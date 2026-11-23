"""Compute all failing degrees for a positive planar Gray base with private updates.

--base JSON uses edges {name:[start,end]}, marks {name:[input path,output path]}
(paths are lists of edge names), and updates [[source mark,target mark],...].
"""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, permutations
import json
from pathlib import Path

from semistrict_surface_interval_degrees import degree_bounds
from semistrict_surface_planar_columns import Column


def spectrum(data):
    edges,marks,updates = data['edges'],data['marks'],data.get('updates',[])
    vertices = {v for e in edges.values() for v in e}
    reach = {v:{v} for v in vertices}
    for a,b in edges.values():
        reach[a].add(b)
    for m in vertices:
        for v in vertices:
            if m in reach[v]:
                reach[v].update(reach[m])

    def poles(path):
        if not path or any(edges[a][1] != edges[b][0] for a,b in zip(path,path[1:])):
            raise ValueError('expected a nonempty composable edge path')
        return edges[path[0]][0],edges[path[-1]][1]
    ends = {}
    for a,(s,t) in marks.items():
        ends[a] = poles(s)
        if ends[a] != poles(t):
            raise ValueError('nonparallel rewrite')
    active = set()
    for a,b in updates:
        if marks[a] != marks[b]:
            raise ValueError('private updates require identical spatial attaching paths')
        active.update((a,b))
    after = {a:[b for b in marks if ends[b][0] in reach[ends[a][1]]] for a in marks}
    for a in after:
        if a in after[a]:
            return {'failing_from':3,'repeatable_mark':a}

    @cache
    def suffix(a):
        extra = max((suffix(b) for b in after[a]),key=lambda t:t[0],default=(0,()))
        return (1+int(a in active)+extra[0], (a,)+extra[1])

    @cache
    def prefix(a):
        extra = max((prefix(b) for b in marks if a in after[b]),key=lambda t:t[0],default=(0,()))
        return (1+int(a in active)+extra[0], extra[1]+(a,))
    best = (0,())
    has_pair = False
    for a in marks:
        for b in after[a]:
            has_pair = True
            left = max((prefix(p) for p in marks if a in after[p]),key=lambda t:t[0],default=(0,()))
            right = max((suffix(q) for q in after[b]),key=lambda t:t[0],default=(0,()))
            if left[1] or right[1]:
                candidate = left[0]+2+right[0],left[1]+(a,b)+right[1]
                if candidate[0] > best[0]:
                    best = candidate
    return {'failing_degrees':([3] if has_pair else [])+list(range(4,best[0]+2)),
            'higher_witness_string':best[1]}


def section(col,order,cut,length):
    """Map wires to ordered target edge words across the selected disjoint boxes."""
    chosen = order[cut:cut+length]
    live = list(col.initial)
    for p in order[:cut]:
        src,dst = col.boxes[p]
        i = live.index(src[0])
        live[i:i+len(src)] = dst
    chosen = tuple(sorted(chosen,key=lambda p:live.index(col.boxes[p][0][0])))
    words = {e:() for e in live}
    for j,p in enumerate(chosen):
        ins,outs = col.boxes[p]
        words[ins[0]] = ((j,0),)
        for i,e in enumerate(outs):
            words[e] = ((j,1),) if i == 0 else ()

    def transport(source,target):
        block = sum((words[e] for e in source),())
        for i,e in enumerate(target):
            words[e] = block if not i else ()
    for p in reversed(order[:cut]):
        a,b = col.boxes[p]
        transport(b,a)
    for p in order[cut+length:]:
        a,b = col.boxes[p]
        transport(a,b)
    assert len(words) == len(col.wires)

    # Reconstruct vertex maps and check both endpoint maps at every face.
    vertex = {}
    def path(edges,offset):
        for e in edges:
            a,b = col.wires[e]
            assert vertex.setdefault(a,offset) == offset
            assert [j for j,_ in words[e]] == list(range(offset,offset+len(words[e])))
            offset += len(words[e])
            assert vertex.setdefault(b,offset) == offset
        return offset
    assert path(col.initial,0) == length
    for p,(a,b) in enumerate(col.boxes):
        pos = vertex[col.wires[a[0]][0]]
        assert path(a,pos) == path(b,pos)
        u,v = (sum((words[e] for e in s),()) for s in (a,b))
        if p in chosen:
            j = chosen.index(p)
            assert u == ((j,0),) and v == ((j,1),)
        else:
            assert u == v
    return max(map(len,words.values()),default=0)


def checks():
    counts = Counter()
    charts = [Column(1,[(0,1,3),(0,1,1),(1,1,2),(3,1,1),(0,4,1)]),
              Column(3,[(1,1,2),(0,1,1),(2,2,1),(0,2,3),(2,1,1)]),
              Column(3,[(2,1,2),(1,1,1),(0,1,1),(2,2,1)])]
    for col in charts:
        for order in permutations(range(len(col.boxes))):
            live = list(col.initial)
            for p in order:
                a,b = col.boxes[p]
                if a[0] not in live:
                    break
                i = live.index(a[0])
                if tuple(live[i:i+len(a)]) != a:
                    break
                live[i:i+len(a)] = b
            else:
                live = list(col.initial)
                for i,p in enumerate(order):
                    for n in range(1,len(order)-i+1):
                        chosen = order[i:i+n]
                        if any(any(e not in live for e in col.boxes[q][0]) for q in chosen):
                            break
                        width = section(col,order,i,n)
                        counts['checked interval projections'] += 1
                        if width > 1:
                            counts['projections with several marked columns on one edge'] += 1
                    a,b = col.boxes[p]
                    k = live.index(a[0])
                    live[k:k+len(a)] = b
    for size in range(1,7):
        labels = tuple(range(size))
        edges = {i:(i,i+1) for i in labels}
        marks = {i:([i],[i]) for i in labels}
        for k in range(size+1):
            for updated in combinations(labels,k):
                result = spectrum({'edges':edges,'marks':marks,'updates':[(i,i) for i in updated]})
                _,mixed = degree_bounds(labels,labels[::-1],updated)
                assert result['failing_degrees'] == ([3] if size>=2 else [])+list(range(4,mixed[0]+2))
                counts['context spectra checked against interval optimization'] += 1
    recurrent = {'edges':{'h':(0,0)},'marks':{'p':(['h'],['h','h'])}}
    assert spectrum(recurrent)['failing_from'] == 3
    for label,n in sorted(counts.items()):
        print(f'{n:,} {label}')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path)
    args = parser.parse_args()
    if args.base:
        print(json.dumps(spectrum(json.loads(args.base.read_text()))))
    else:
        checks()
