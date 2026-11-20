"""Build the finite witness product for monotone resources over a binary order."""

from itertools import combinations, product

from homotopy_polygraph_milestones import binary_pairs, compact, milestones, orders
from homotopy_polygraph_monotone import (cellular_profile, incidence_record, product_boundary,
                                         witness_product)
from homotopy_polygraph_two_resources import profiles


def record(programs, initial, serial, many, binary):
    states = profiles(programs,initial)
    h = orders(programs,states,serial,binary_pairs(states,binary))
    axes, events = milestones(states,many)
    renamed = {e:(i,j) for i,row in enumerate(events) for j,e in enumerate(row)}
    order = {new:{renamed[f] for f in h[e] if f in renamed} for e,new in renamed.items()}
    levels = witness_product(axes,len(many),order)
    return levels, cellular_profile(levels,product_boundary)


def corner_nerve(factors, vertices, forbidden):
    """Component nerve of the cover excluding one coordinate of a missing corner."""
    assert forbidden not in vertices
    parts = {}
    levels = [[] for _ in factors]
    for size in range(1,len(factors)+1):
        for omit in combinations(range(len(factors)),size):
            remaining = {v for v in vertices if all(v[i] != forbidden[i] for i in omit)}
            group = {}
            while remaining:
                start = min(remaining)
                remaining.remove(start)
                stack = [start]
                while stack:
                    node = stack.pop()
                    group[node] = start
                    for i,factor in enumerate(factors):
                        for x in factor:
                            adj = node[:i]+(x,)+node[i+1:]
                            if adj in remaining:
                                remaining.remove(adj)
                                stack.append(adj)
                levels[size-1].append((omit,start))
            parts[omit] = group
    while levels and not levels[-1]:
        levels.pop()

    def facets(cell):
        omit, rep = cell
        for i in range(len(omit)):
            parent = omit[:i]+omit[i+1:]
            yield (parent,parts[parent][rep]), (-1)**i
    return cellular_profile(levels,facets)


def check_corner_nerve():
    # All proper faces of the 3-cube are squares or smaller. Every induced
    # subcomplex of such a face has contractible components.
    factors = [(0,1)]*3
    corners = list(product(*factors))
    square_faces = [list(combinations((0,1),n)) for n in (1,2)]
    choices = square_faces[0] + square_faces[1]
    cells = [(cell,set(product(*cell))) for cell in product(choices,repeat=3)]
    bad = 0
    for mask in range((1<<len(corners))-1):
        vertices = {v for i,v in enumerate(corners) if mask & (1<<i)}
        levels = [[] for _ in range(4)]
        for cell, points in cells:
            if points <= vertices:
                levels[sum(len(f)-1 for f in cell)].append(cell)
        while levels and not levels[-1]:
            levels.pop()
        expected = cellular_profile(levels,product_boundary)
        result = corner_nerve(factors,vertices,min(set(corners)-vertices))
        assert result == expected
        bad += bool(result[1])
    print(f'255 proper vertex subsets of the 3-cube agree with their corner nerves; {bad} have H1.')


def check():
    check_corner_nerve()
    # A genuinely reversing binary resource, two monotone guards, and two
    # different binary exchange components at the same endpoints.
    wrapped = lambda r: [('P',2), ('P',r), ('V',1-r), ('V',2)]
    programs = [wrapped(0),wrapped(1),[('P',0),('V',1)],[('P',1),('V',0)]]
    initial = [(0,1,0),(1,0,0),(0,1,1),(1,0,1)]
    for a,b in ((0,1),(1,0)):
        serial = [a]*4+[b]*4+[2]*2+[3]*2
        levels, (h0,higher) = record(programs,initial,serial,(0,1),(2,))
        states = profiles(programs,initial)
        h = orders(programs,states,serial,binary_pairs(states,(2,)))
        betti = compact(states,(0,1),h)[2]
        assert not any(t for _,t in higher)
        assert (h0,*(rank for rank,_ in higher)) == betti
        corners = {tuple(f[0] for f in cell) for cell in levels[0]}
        factors = [sorted(values) for values in map(set,zip(*corners))]
        for w in set(product(*factors))-corners:
            assert corner_nerve(factors,corners,w) == (h0,higher)
        print(f'Binary component {a} before {b}: {list(map(len,levels))} cells, Betti {betti}.')

    facets = [(0,1,2),(1,2,3),(2,3,4),(0,3,4),(0,1,4),
              (0,2,5),(1,3,5),(2,4,5),(0,3,5),(1,4,5)]
    for faces,extend in [(facets,False), ([(0,1),(1,2),(2,0)],True)]:
        n = 1+max(max(s) for s in faces)
        m = len(faces)
        missing = [(i,j) for i in range(n) for j,f in enumerate(faces) if i not in f]
        words,holds = incidence_record(n+int(extend),m,missing)
        start = n+int(extend)
        serial = [i for r in (range(start,len(words)),range(start)) for i in r for _ in words[i]]
        args = (serial,(0,),range(1,len(missing)+1))
        levels,profile = record(words,holds,*args)
        if extend:
            assert profile == (1,())
            holds[n][0] += 1
            _,profile = record(words,holds,*args)
            assert profile == (1,((1,()),))
            print('Suppressing the extra arrival changes a contractible fibre to a circle.')
        else:
            assert profile == (1,((0,(2,)),))
            print(f'Projective plane: {list(map(len,levels))} cells, H1 = Z/2.')

    for size in (4,8,12):
        # Each axis can contribute only one signed change to this guard.
        axes = [(1,0)]*size+[(0,1)]*size
        empty = {(i,0):set() for i in range(2*size)}
        if size <= 4:
            levels = witness_product(axes,1,empty)
            assert sum(map(len,levels)) == (2**size-1)**2
        print(f'{size}+{size} free witnesses: {(2**size-1)**2:,} product cells, '
              f'{2**(size*size)-1:,} nonempty witness-nerve faces.')


if __name__ == '__main__':
    check()
