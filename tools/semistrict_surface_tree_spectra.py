"""Compute context-wide Gray spectrum bounds for finite globular generators.

A base has 'edges' as pairs of object poles and 'slots' as [source object,
target object, maximum local globe dimension] for its occupied short homs.
Repeated spatial use is permitted. Trees in the checks are lists of children.
"""

from argparse import ArgumentParser
from collections import defaultdict
from functools import cache
from itertools import product
import json
from pathlib import Path

from semistrict_surface_square_quotient_chains import Space


class Tree:
    def __init__(self, children):
        self.layers = defaultdict(list)
        self.layers[0] = list(range(len(children)+1))
        self.faces = {}
        for i,subtree in enumerate(children):
            child = Tree(subtree)
            for d,layer in child.layers.items():
                for x in layer:
                    self.layers[d+1].append((i,x))
                    self.faces[i,x] = tuple((i,y) for y in child.faces[x]) if d else (i,i+1)
        self.height = max(self.layers)


def cycles(trees):
    heights = [t.height for t in trees]
    minimum = min(a+b for a,b in zip(heights,heights[1:]))
    words = set()
    for i in range(len(trees)-1):
        if heights[i]+heights[i+1] == minimum:
            dims = tuple(1 if j in (i,i+1) else h for j,h in enumerate(heights))
            for cells in product(*(t.layers[d] for t,d in zip(trees,dims))):
                words.add(tuple(zip(dims,cells)))
    image = Space()
    for w in sorted(words):
        sign = 1
        row = {}
        for j,(d,x) in enumerate(w):
            a,b = trees[j].faces[x]
            row[w[:j]+((d-1,a),)+w[j+1:]] = -sign
            row[w[:j]+((d-1,b),)+w[j+1:]] = sign
            sign *= (-1)**d
        image.insert(row)
    return len(words)-len(image.rows)


def context_spectrum(data):
    slots = data['slots']
    edges = data['edges']
    vertices = {v for edge in edges for v in edge} | {v for a,b,_ in slots for v in (a,b)}
    reach = {v:{v} for v in vertices}
    for a,b in edges:
        reach[a].add(b)
    for a in vertices:
        for v in vertices:
            if a in reach[v]:
                reach[v].update(reach[a])
    edge_pairs = {tuple(edge) for edge in edges}
    for a,b,d in slots:
        if d<1 or (a,b) not in edge_pairs:
            raise ValueError('an occupied globular slot needs positive height and a parallel generating edge')
        if a in reach[b]:
            return {'failing_from':3}
    after = [[j for j,(b,_,_) in enumerate(slots) if b in reach[end]] for _,end,_ in slots]
    before = [[j for j,seq in enumerate(after) if i in seq] for i in range(len(slots))]

    @cache
    def tail(i):
        return slots[i][2]+max((tail(j) for j in after[i]),default=0)

    @cache
    def head(i):
        return slots[i][2]+max((head(j) for j in before[i]),default=0)

    best = 0
    exceptional = False
    for i,rest in enumerate(after):
        for j in rest:
            best = max(best,2+max((head(k) for k in before[i]),default=0)
                       + max((tail(k) for k in after[j]),default=0))
            if slots[i][2]>=2 and slots[j][2]>=3:
                exceptional |= any(slots[k][2]>=2 for k in after[j])
    return {'failing_degrees':list(range(3,best+2)),
            'undetermined_degrees':[6] if best==4 and exceptional else []}


def checks():
    tree_types = [([],[]), ([[]],[[],[]]), ([[[]]],[]), ([[[],[]]],)]
    checked = singular = 0
    for width in range(2,5):
        for shapes in product(tree_types,repeat=width):
            trees = [Tree(s) for s in shapes]
            h = [t.height for t in trees]
            special = (width==2 and min(h)>=2) or (width==3 and h[0]==h[-1]==2 and h[1]>=2)
            n = cycles(trees)
            assert special or n == 0
            checked += 1
            singular += n>0
    for shape,known,possible in [
        ((2,4,2),[3,4,5],[6]), ((2,2,2),[3,4,5],[]),
        ((3,4,2),[3,4,5,6],[]), ((2,7),[3],[]), ((1,),[],[])]:
        size = len(shape)
        data = {'edges':[(j,j+1) for j in range(size)],'slots':[(j,j+1,h) for j,h in enumerate(shape)]}
        assert context_spectrum(data)=={'failing_degrees':known,'undetermined_degrees':possible}
    assert context_spectrum({'edges':[(0,1),(1,0)],'slots':[(0,1,7)]}) == {'failing_from':3}
    print(f'{checked} branching tree tensors checked; {singular} have top relation cycles')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path)
    args = parser.parse_args()
    if args.base:
        print(json.dumps(context_spectrum(json.loads(args.base.read_text()))))
    else:
        checks()
