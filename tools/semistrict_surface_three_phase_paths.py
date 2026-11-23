"""Decide a local-rank-five comparison at three updated slots by their phase paths.

Use --faces FILE on parallel strict rank-four tableaux. Supply their sparse
top chains as [cell, coefficient] pairs in 'source' and 'target', and the phase
triple of their common triple-cube source as 'start' (null if it is absent).
Each cell is a list of [local degree, vertex/phase/update index] pairs.
"""

from argparse import ArgumentParser
from collections import Counter, defaultdict, deque
from itertools import permutations, product
import json
from pathlib import Path

from semistrict_surface_penultimate_intervals import boundary


def clean(chain):
    return {c:n for c,n in chain.items() if n}


def differential(chain):
    result = Counter()
    for cell,n in chain.items():
        for face,sign in boundary(cell):
            result[face] += n*sign
    return clean(result)


def difference(target,source):
    result = Counter(target)
    result.subtract(source)
    return clean(result)


def step(vertex,axis):
    nxt = list(vertex)
    nxt[axis] += -1 if axis == 1 else 1
    return tuple(nxt)


def segment_cell(vertex,axes):
    """Lift a unit oriented phase edge, square, or cube to its all-active word."""
    return tuple((2,j-int(i==1)) if i in axes else (1,j) for i,j in enumerate(vertex))


def phase_path(start,face):
    edges = defaultdict(list)
    length = 0
    for cell,n in face.items():
        if any(d == 0 for d,_ in cell):
            continue
        if n != 1 or sum(d for d,_ in cell) != 4:
            raise ValueError('invalid positive all-active edge')
        axis, = [i for i,(d,_) in enumerate(cell) if d == 2]
        v = tuple(j+int(i==axis==1) for i,(_,j) in enumerate(cell))
        edges[v].append(axis)
        length += 1
    v = start
    word = []
    while edges.get(v):
        if len(edges[v]) != 1:
            raise ValueError('the integral edge flow branches')
        axis = edges[v].pop()
        word.append(axis)
        v = step(v,axis)
    if len(word) != length:
        raise ValueError('edge flow does not begin at the specified cube')
    return tuple(word),v


def sorting_chain(start,source,target):
    if Counter(source) != Counter(target):
        raise ValueError('phase paths must have common ends')
    current = list(source)
    chain = Counter()
    for i,need in enumerate(target):
        j = current.index(need,i)
        while j > i:
            left,right = current[j-1:j+1]
            if left < right:
                return None
            vertex = start
            for axis in current[:j-1]:
                vertex = step(vertex,axis)
            chain[segment_cell(vertex,(left,right))] += 1
            current[j-1:j+1] = right,left
            j -= 1
    return clean(chain)


def compare(start,source,target):
    if differential(source) != differential(target):
        raise ValueError('the supplied top rows do not have a shared boundary')
    u,end = phase_path(start,source)
    v,end2 = phase_path(start,target)
    if end != end2:
        raise ValueError('phase endpoints differ')
    chain = sorting_chain(start,u,v)
    if chain is not None and differential(chain) != difference(target,source):
        raise ValueError('rank-four rows do not form the stated parallel tableaux')
    return chain


def word_chain(start,word):
    result = Counter()
    vertex = start
    for a in word:
        result[segment_cell(vertex,(a,))] += 1
        vertex = step(vertex,a)
    return result


def checks():
    tested = positive = 0
    for mult in [(1,1,1),(1,2,2),(2,1,3)]:
        words = set(permutations(tuple(i for i,n in enumerate(mult) for _ in range(n))))
        start = (1,mult[1]+2,3)
        chains = {w:word_chain(start,w) for w in words}
        for source in words:
            # Independent directed rewriting graph on all shuffle paths.
            queue, reachable = deque([source]), {source}
            while queue:
                now = queue.popleft()
                for i,(a,b) in enumerate(zip(now,now[1:])):
                    if a > b:
                        nxt = now[:i]+(b,a)+now[i+2:]
                        if nxt not in reachable:
                            reachable.add(nxt)
                            queue.append(nxt)
            for target in words:
                z = sorting_chain(start,source,target)
                assert (z is not None) == (target in reachable)
                tested += 1
                if z is None:
                    continue
                positive += 1
                diff = differential(z)
                active = {c:n for c,n in diff.items() if all(d for d,_ in c)}
                assert active == difference(chains[target],chains[source])
                # Supply the omitted stationary-vertex rows from the signed
                # boundary itself, then check reconstruction of every component.
                s,t = Counter(chains[source]),Counter(chains[target])
                for c,n in diff.items():
                    if any(d==0 for d,_ in c):
                        (t if n>0 else s)[c] += abs(n)
                assert compare(start,s,t) == z
    # Actual parallel 4-tableaux from the characteristic 5-atoms and their
    # reverses in the three-globe chart. Their common preceding 3-row gives
    # the unique full triple. No stationary-vertex data are manufactured.
    from gray_globe_comparison import atom
    native = 0
    for axis,phase in product(range(3),range(2)):
        basis = tuple((1,phase) if i == axis else (2,2) for i in range(3))
        rows = atom(basis)
        def translate(cell):
            return tuple((d,0 if d==2 else j) for d,j in cell)
        s,t = [Counter(translate(c) for c in row) for row in rows[4]]
        full, = [c for c in rows[3][0] if all(d==1 for d,_ in c)]
        start = tuple(j for _,j in full)
        assert compare(start,s,t) == {translate(basis):1}
        assert compare(start,t,s) is None
        native += 2
    print(f'{tested:,} phase-path comparisons, {positive:,} complete boundary reconstructions, '
          f'{native} signed native tests at actual tableau faces')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces',type=Path)
    args = parser.parse_args()
    if args.faces:
        data = json.loads(args.faces.read_text())
        def parse(rows):
            return {tuple(map(tuple,c)):n for c,n in rows if n}
        start = tuple(data['start']) if data['start'] is not None else None
        z = compare(start,parse(data['source']),parse(data['target']))
        print(json.dumps(None if z is None else [[c,n] for c,n in z.items()]))
    else:
        checks()
