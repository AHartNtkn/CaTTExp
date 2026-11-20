"""Compile a CNF solution complex into an explicitly sized monotone comparison."""

from itertools import combinations, combinations_with_replacement, product

from homotopy_polygraph_milestones import binary_pairs, milestones, orders
from homotopy_polygraph_monotone import (cellular_profile, product_boundary,
                                         witness_product)
from homotopy_polygraph_two_resources import profiles


def formula_record(n, clauses):
    """One high guard per variable/clause and one binary link per forced comparison."""
    # Each guard has source actors (departures) and sink actors (arrivals).
    departures = [(g,i) for g in range(n) for i in (0,1)]
    departures += [(n+j,0) for j in range(len(clauses))]
    arrivals = [(g,0) for g in range(n)]
    arrivals += [(n+j,k) for j,c in enumerate(clauses) for k in range(len(c))]
    high = n+len(clauses)
    words = [[('P',g)] for g,_ in departures]+[[] for _ in arrivals]
    holds = [[1]*high for _ in words]
    for i,(g,_) in enumerate(departures):
        holds[i][g] = 0
    links = []
    for j,(g,b) in enumerate(departures):
        for i,(h,k) in enumerate(arrivals,len(departures)):
            universal = g >= n and h < n
            conflict = False
            if g < n <= h:
                literal = clauses[h-n][k]
                conflict = abs(literal) == g+1 and bool(b) != (literal > 0)
            if universal or conflict:
                r = high+len(links)
                links.append((j,i))
                words[j].append(('V',r))
                words[i].append(('P',r))
                for a,row in enumerate(holds):
                    row.append(int(a != i))
    for i,(g,_) in enumerate(arrivals,len(departures)):
        words[i].append(('V',g))
    serial = [a for a,w in enumerate(words) for _ in w]
    states = profiles(words,holds)
    h = orders(words,states,serial,binary_pairs(states,range(high,high+len(links))))
    actual = {(j,i) for j in range(len(departures)) for i in range(len(departures),len(words))
              if (i,len(words[i])-1) in h[j,0]}
    assert actual == set(links)
    axes, events = milestones(states,range(high))
    names = {e:(a,0) for a,row in enumerate(events) for e in row}
    reduced = {v:{names[f] for f in h[e] if f in names} for e,v in names.items()}
    return axes, high, reduced, departures, arrivals, words, holds, h


def lift_corner(bits, witnesses, departures, arrivals, words, holds, order):
    """Return an actual main- and binary-legal serialization of this corner."""
    n = len(bits)
    successors = {e:set(fs) for e,fs in order.items()}
    for g in range(n+len(witnesses)):
        source = departures.index((g,bits[g] if g<n else 0))
        sink = len(departures)+arrivals.index((g,0 if g<n else witnesses[g-n]))
        successors[sink,len(words[sink])-1].add((source,0))
    degrees = dict.fromkeys(successors,0)
    for fs in successors.values():
        for f in fs:
            degrees[f] += 1
    ready = [e for e,d in degrees.items() if d==0]
    current = [list(row) for row in holds]
    free = [sum(row[r] == 0 for row in current) for r in range(len(holds[0]))]
    assert all(free)
    serial = []
    while ready:
        a,i = ready.pop()
        op,r = words[a][i]
        old = current[a][r]
        current[a][r] += 1 if op == 'P' else -1
        free[r] += int(current[a][r] == 0) - int(old == 0)
        assert current[a][r] >= 0 and free[r]>0
        serial.append(a)
        for f in successors[a,i]:
            degrees[f] -= 1
            if degrees[f] == 0:
                ready.append(f)
    assert len(serial) == len(degrees)
    return serial


def components(vertices):
    remaining = set(vertices)
    result = set()
    while remaining:
        seed = remaining.pop()
        reached = {seed}
        stack = [seed]
        while stack:
            v = stack.pop()
            newly = {w for w in remaining if sum(a != b for a,b in zip(v,w)) == 1}
            remaining.difference_update(newly)
            reached.update(newly)
            stack.extend(newly)
        result.add(frozenset(reached))
    return result


def check_formula(n, clauses, homology=False):
    axes, r, h, departures, arrivals, words, holds, order = formula_record(n,clauses)
    levels = witness_product(axes,r,h)
    cube = {}
    for bits in product((0,1),repeat=n):
        supports = [[k for k,x in enumerate(c) if bits[abs(x)-1] == (x>0)] for c in clauses]
        if all(supports):
            cube[bits] = set(product(*supports))
    expected = {bits+w for bits,choices in cube.items() for w in choices}
    corners = set()
    for cell in levels[0] if levels else ():
        bits = tuple(departures[cell[2*g+1][0][0]][1] for g in range(n))
        choices = tuple(arrivals[cell[2*j][0][0]-len(departures)][1] for j in range(n,r))
        corners.add(bits+choices)
    assert corners == expected
    for v in corners:
        lift_corner(v[:n],v[n:],departures,arrivals,words,holds,order)
    assert {frozenset(w[:n] for w in part) for part in components(corners)} == components(cube)
    if homology:
        bool_cells = [[] for _ in range(n+1)]
        for face in product(((0,),(1,),(0,1)),repeat=n):
            if set(product(*face)) <= cube.keys():
                bool_cells[sum(len(f)-1 for f in face)].append(face)
        while bool_cells and not bool_cells[-1]:
            bool_cells.pop()
        ordinary = cellular_profile(bool_cells,product_boundary)
        assert ordinary == cellular_profile(levels,product_boundary)
        return ordinary


def check():
    literals = (1,-1,2,-2)
    types = [(l,) for l in literals]+[(a,b) for a,b in combinations(literals,2) if a != -b]
    count = 0
    for clauses in combinations_with_replacement(types,2):
        check_formula(2,clauses)
        count += 1
    print(f'{count} two-variable CNFs agree on all lifted corners and connected components.')
    neq = ((1,2),(-1,-2))
    assert check_formula(2,neq,True) == (2,())
    print('Exclusive-or gives two strict labels at the designated record.')
    cycle = ((1,2,3),(-1,-2,-3))
    assert check_formula(3,cycle,True) == (1,((1,()),))
    print('The cube with two opposite vertices omitted gives one strict label with H1 = Z.')


if __name__ == '__main__':
    check()
