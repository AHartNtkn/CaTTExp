"""Decide strict comparisons in the tensor of two positive planar rule diagrams.

Each column starts with an ordered path, then replaces nonempty contiguous
subpaths by nonempty fresh paths. The top chains use IDs [degree,index].
"""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from itertools import product
import json
from pathlib import Path


def add(target, source, scale=1):
    for key, value in source.items():
        target[key] += scale * value


def clean(chain):
    return {x: n for x, n in chain.items() if n}


class Column:
    def __init__(self, width, schedule):
        self.vertices = list(range(width + 1))
        self.wires = [(i, i+1) for i in range(width)]
        self.initial = tuple(range(width))
        self.boxes = []
        current = self.initial
        for i, a, b in schedule:
            if a < 1 or b < 1 or i < 0 or i+a > len(current):
                raise ValueError('invalid positive polygon')
            inputs = current[i:i+a]
            inner = tuple(range(len(self.vertices),len(self.vertices)+b-1))
            self.vertices.extend(inner)
            vertices = (self.wires[inputs[0]][0],) + inner + (self.wires[inputs[-1]][1],)
            outputs = tuple(range(len(self.wires),len(self.wires)+b))
            self.wires.extend(zip(vertices,vertices[1:]))
            self.boxes.append((inputs,outputs))
            current = current[:i] + outputs + current[i+a:]
        self.final = current
        self.producer = {e:p for p,(_,out) in enumerate(self.boxes) for e in out}
        self.consumer = {e:p for p,(inp,_) in enumerate(self.boxes) for e in inp}
        self.rootpaths = {0:Counter()}
        while len(self.rootpaths) < len(self.vertices):
            for i,(v,w) in enumerate(self.wires):
                if v in self.rootpaths and w not in self.rootpaths:
                    self.rootpaths[w] = self.rootpaths[v] + Counter({(1,i):1})

    def boundary(self, cell):
        d,i = cell
        result = Counter()
        if d == 1:
            u,v = self.wires[i]
            result[0,v] += 1
            result[0,u] -= 1
        elif d == 2:
            a,b = self.boxes[i]
            result.update((1,e) for e in b)
            result.subtract((1,e) for e in a)
        return result

    def homotopy(self, cell):
        d,i = cell
        if d == 0:
            return self.rootpaths[i]
        result = Counter()
        if d == 1:
            v,w = self.wires[i]
            cycle = Counter({cell:1})
            add(cycle,self.rootpaths[v])
            add(cycle,self.rootpaths[w],-1)
            for p in reversed(range(len(self.boxes))):
                n = cycle[1,self.boxes[p][1][0]]
                result[2,p] = n
                add(cycle,self.boundary((2,p)),-n)
            assert not clean(cycle)
        return result

    def routes(self):
        def walk(edges, boxes):
            p = self.consumer.get(edges[-1])
            if p is None:
                yield frozenset((1,e) for e in edges) | frozenset((2,b) for b in boxes)
            else:
                for out in self.boxes[p][1]:
                    yield from walk(edges+(out,), boxes+(p,))
        for e in self.initial:
            yield from walk((e,),())


def tensor_boundary(left,right,z):
    result = Counter()
    for (a,b),v in z.items():
        for u,n in left.boundary(a).items():
            result[u,b] += v*n
        for u,n in right.boundary(b).items():
            result[a,u] += (-1)**a[0]*v*n
    return clean(result)


def fill_cycle(left,right,z):
    result = Counter()
    for (a,b),v in z.items():
        for u,n in left.homotopy(a).items():
            result[u,b] += n*v
        if a[0] == 0:
            for u,n in right.homotopy(b).items():
                result[(0,0),u] += n*v
    if tensor_boundary(left,right,result) != clean(z):
        raise ValueError('difference is not a positive-degree cycle')
    return clean(result)


def arcs(left,right,z):
    def pair(i,j):
        return None if i is None or j is None else (i,j)
    for p in range(len(left.boxes)):
        for e in range(len(right.wires)):
            cell = (2,p),(1,e)
            yield pair(p,right.producer.get(e)), pair(p,right.consumer.get(e)), z.get(cell,0), cell
    for q in range(len(right.boxes)):
        for e in range(len(left.wires)):
            cell = (1,e),(2,q)
            yield pair(left.producer.get(e),q), pair(left.consumer.get(e),q), z.get(cell,0), cell


def potentials(edges):
    edges = list(edges)
    nodes = {x for u,v,_,_ in edges for x in (u,v)} | {None}
    distance = dict.fromkeys(nodes,0)
    for _ in nodes:
        changed = False
        for u,v,c,_ in edges:
            if distance[v] > distance[u] + c:
                distance[v] = distance[u] + c
                changed = True
        if not changed:
            return {x:d-distance[None] for x,d in distance.items()}
    return None


def solve(left,right,degree,difference):
    """Local filler degree 3 or 4 at given parallel tableau faces."""
    z = fill_cycle(left,right,difference)
    if degree == 4:
        return z if all(n >= 0 for n in z.values()) else None
    if degree != 3:
        raise ValueError('expected local rank 3 or 4')
    dist = potentials(arcs(left,right,z))
    if dist is None:
        return None
    adjustment = {
        ((2,node[0]),(2,node[1])):n for node,n in dist.items() if node is not None}
    out = Counter(z)
    add(out,tensor_boundary(left,right,adjustment))
    assert all(n >= 0 for n in out.values()) and tensor_boundary(left,right,out) == clean(difference)
    return clean(out)


def readings(left,right):
    def initial(side,edges):
        return tuple((side,e) for e in edges)
    start = initial(1,right.initial) + initial(0,left.initial)
    end = initial(0,left.final) + initial(1,right.final)
    columns = left,right
    def walk(order,used,chain,letters):
        if order == end and len(used) == len(left.boxes)+len(right.boxes):
            yield letters,chain
        for i,((s,b),(t,a)) in enumerate(zip(order,order[1:])):
            if (s,t) == (1,0):
                cell = (1,a),(1,b)
                yield from walk(order[:i]+((0,a),(1,b))+order[i+2:],used,chain+Counter({cell:1}),
                                letters+(('X',a,b),))
        for side,col in enumerate(columns):
            other = columns[1-side]
            for p,(ins,outs) in enumerate(col.boxes):
                if (side,p) in used or (side,ins[0]) not in order:
                    continue
                i = order.index((side,ins[0]))
                if order[i:i+len(ins)] != initial(side,ins):
                    continue
                earlier = [e for s,e in order[:i] if s != side]
                v = other.wires[earlier[-1]][1] if earlier else 0
                cell = ((2,p),(0,v)) if not side else ((0,v),(2,p))
                yield from walk(order[:i]+initial(side,outs)+order[i+len(ins):],used|{(side,p)},
                                chain+Counter({cell:1}),letters+(('P',side,p),))
    return dict(walk(start,set(),Counter(),()))


def check_pair(left,right,counts):
    data = readings(left,right)
    def key(z):
        return tuple(sorted(z.items()))
    chains = {key(z) for z in data.values()}
    def support(op):
        if op[0] == 'X':
            return {(0,op[1]),(1,op[2])}
        _, side, index = op
        sources,targets = (left,right)[side].boxes[index]
        return {(side,e) for e in sources + targets}

    # Check the strict equality classes independently of the tensor tableaux.
    unseen = set(data)
    representatives = set()
    while unseen:
        seed = unseen.pop()
        z = key(data[seed])
        assert z not in representatives
        representatives.add(z)
        stack = [seed]
        while stack:
            w = stack.pop()
            for i,(a,b) in enumerate(zip(w,w[1:])):
                if support(a).isdisjoint(support(b)):
                    v = w[:i]+(b,a)+w[i+2:]
                    assert key(data[v]) == z
                    if v in unseen:
                        unseen.remove(v)
                        stack.append(v)
    assert representatives == chains
    graph = defaultdict(set)
    for w,z in data.items():
        for i,op in enumerate(w):
            if op[0] != 'P':
                continue
            _,side,p = op
            own,other = (left,right) if side == 0 else (right,left)
            a,b = own.boxes[p]
            for e in range(len(other.wires)):
                if side == 0:
                    lhs = tuple(('X',j,e) for j in a)+(op,)
                    rhs = (op,)+tuple(('X',j,e) for j in b)
                    start = i-len(a)
                else:
                    lhs = (op,)+tuple(('X',e,j) for j in reversed(b))
                    rhs = tuple(('X',e,j) for j in reversed(a))+(op,)
                    start = i
                if start >= 0 and w[start:start+len(lhs)] == lhs:
                    other_word = w[:start]+rhs+w[start+len(lhs):]
                    graph[key(z)].add(key(data[other_word]))
    for s in chains:
        seen,stack = {s},[s]
        while stack:
            for v in graph[stack.pop()] - seen:
                seen.add(v)
                stack.append(v)
        for t in chains:
            diff = Counter(dict(t))
            diff.subtract(dict(s))
            z = fill_cycle(left,right,diff)
            good = solve(left,right,3,diff) is not None
            assert good == (t in seen)
            edges = list(arcs(left,right,z))
            for_all = all(potentials([edge for edge in edges if edge[3][0] in l and edge[3][1] in r]) is not None
                          for l,r in product(left.routes(),right.routes()))
            assert for_all == good
            counts['typed degree-four decisions'] += 1
    counts['literal planar readings'] += len(data)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces',type=Path,help='columns [width,schedule], local degree, and signed target-minus-source chain')
    args = parser.parse_args()
    if args.faces:
        d = json.loads(args.faces.read_text())
        cols = [Column(*x) for x in d['columns']]
        diff = Counter()
        for a,b,n in d['difference']:
            diff[tuple(a),tuple(b)] += n
        ans = solve(*cols,d['degree'],diff)
        print(json.dumps(None if ans is None else [[a,b,n] for (a,b),n in ans.items()]))
    else:
        totals = Counter()
        bare = Column(1,[])
        split = Column(1,[(0,1,2)])
        merge = Column(2,[(0,2,1)])
        diamond = Column(1,[(0,1,2),(0,2,1)])
        two = Column(2,[(0,1,1),(1,1,1)])
        for l,r in ((split,bare),(bare,merge),(split,merge),(diamond,split),(two,merge)):
            check_pair(l,r,totals)
        for l,r in ((diamond,two),(split,merge)):
            for signs in product((-1,0,1),repeat=len(l.boxes)*len(r.boxes)):
                z = {((2,i),(2,j)):signs[i*len(r.boxes)+j]
                     for i,j in product(range(len(l.boxes)),range(len(r.boxes)))}
                answer = solve(l,r,4,tensor_boundary(l,r,z))
                assert (answer is not None) == (min(signs)>=0)
                totals['degree-five coefficient decisions'] += 1
        for label,count in sorted(totals.items()):
            print(f'{count:,} {label}')
