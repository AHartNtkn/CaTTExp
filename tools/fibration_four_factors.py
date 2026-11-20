#!/usr/bin/env python3
"""Check marked 4-factor reachability at the poles of the D^3 x D^2 Gray atom."""
from itertools import combinations, product
from gray_globe_comparison import atom, close_atoms, face, globe, strict_cells


def rank(cell):
    pure = crossing = 0
    for (fdim, ftag), (bdim, btag) in cell[-1][0]:
        if fdim == 2 and bdim == 0:
            pure += (2 if ftag == 0 else 1) * (3 if btag == 0 else 1)
        if fdim == bdim == 1:
            crossing += 1 if btag == 0 else 2
    return pure, crossing


def reachable(start, edges):
    visited, stack = {start}, [start]
    while stack:
        for target in edges[stack.pop()]:
            if target not in visited:
                visited.add(target)
                stack.append(target)
    return visited


def check():
    shape = (3, 2)
    top = atom(((3, 2), (2, 2)))
    lower, upper = face(top, 0), face(top, 1)
    source, target = face(lower, 0), face(lower, 1)
    assert (source, target) == (face(upper, 0), face(upper, 1))
    all_three = strict_cells(shape, 3)
    nonidentity = [c for c in all_three if c[-1][0]]
    assert all(rank(face(c, 0)) > rank(face(c, 1)) for c in nonidentity)
    middle = {c for c in all_three if c[:-1] == source[:-1]}
    labels = list(product(globe(3), globe(2)))
    low_atoms = [atom(z) for z in labels if sum(x[0] for x in z) <= 3]
    high = [z for z in labels if sum(x[0] for x in z) == 4]
    moves = [(face(c, 0), c[-1][0][0], face(c, 1))
             for c in strict_cells(shape, 4)
             if len(c[-1][0]) == 1 and face(c, 0) in middle]
    facets = [set(c[-1][0]) for c in (lower, upper)]
    checked = accepted = 0
    for size in range(len(high) + 1):
        for subset in combinations(high, size):
            allowed = set(subset)
            edges = {u: set() for u in middle}
            for u, z, v in moves:
                if z in allowed:
                    edges[u].add(v)
            # An independent computation closes the chosen atoms under *all* strict compositions.
            direct = {(face(c, 0), face(c, 1))
                      for c in close_atoms(low_atoms + [atom(z) for z in allowed], 4)
                      if face(c, 0) in middle}
            graph = {(u, v) for u in middle for v in reachable(u, edges)}
            assert direct == graph
            exists = (source, target) in graph
            assert exists == any(f <= allowed for f in facets)
            accepted += exists
            checked += 1
    print(f"strict 3-cells={len(all_three)}, strict rank descents={len(nonidentity)}, "
          f"parallel middle cells={len(middle)}, elementary 4-steps={len(moves)}")
    print(f"allowed-generator subsets={checked}, admitting the diagonal factor={accepted}")
    assert (len(middle), len(moves), checked, accepted) == (4, 4, 16, 7)


if __name__ == "__main__":
    check()
