"""Project a suspended cube to a simplex and isolate the RC comparisons at its cuts."""
from collections import Counter
from functools import cache
from itertools import combinations, product

from gray_globe_comparison import close_atoms
from relative_coherence_cube_boundary import boundary
from relative_coherence_steiner_cuts import tableau


def simplex_d(simplex):
    return Counter({simplex[:j] + simplex[j+1:]: (-1)**j for j in range(len(simplex))})


@cache
def simplex_atom(simplex):
    sides = []
    for sign in (-1, 1):
        row = Counter({simplex: 1})
        chain = [tuple(row)]
        for _ in simplex[1:]:
            differential = Counter()
            for cell, n in row.items():
                for face, a in simplex_d(cell).items():
                    differential[face] += sign*n*a
            row = +differential
            chain.append(tuple(sorted(row.elements())))
        sides.append(chain[::-1])
    return tuple(zip(*sides))


def intervals(face):
    fixed = (0, *(i for i, a in enumerate(face, 1) if a == 1), len(face)+1)
    return tuple(zip(fixed, fixed[1:]))


@cache
def image_basis(face):
    active = tuple(i for i, a in enumerate(face, 1) if a == 0)
    blocks = intervals(face)
    if not active:
        return blocks
    for lo, hi in blocks:
        if lo < active[0] and active[-1] < hi:
            return ((lo, *active, hi),)
    return ()


def push(chain):
    return tuple(sorted(simplex for f in chain for simplex in image_basis(f)))


def image_rows(face):
    poles = (((0,),), ((len(face)+1,),))
    return (poles, *((push(s), push(t)) for s,t in tableau(face)))


def wedge_rows(face):
    """Horizontal composite of the individual atoms, padded by identities."""
    height = face.count(0)+1
    rows = [[[], []] for _ in range(height+1)]
    for lo, hi in intervals(face):
        active = tuple(i for i in range(lo+1, hi) if face[i-1] == 0)
        for j, pair in enumerate(simplex_atom((lo,*active,hi))):
            for side in (0, 1):
                rows[j][side].extend(pair[side])
    rows[0] = [[(0,)], [(len(face)+1,)]]
    return tuple(tuple(tuple(sorted(chain)) for chain in pair) for pair in rows)


def support(rows):
    maximal = {s for pair in rows for chain in pair for s in chain}
    return {f for s in maximal for size in range(1, len(s)+1) for f in combinations(s, size)}


def census(n):
    for f in product((-1,0,1), repeat=n-1):
        differential = Counter()
        for s in image_basis(f):
            differential.update(simplex_d(s))
        expected = Counter()
        if 0 in f:
            for child, a in boundary(f):
                for s in image_basis(child):
                    expected[s] += a
        else:
            expected[(n,)] = 1
            expected[(0,)] = -1
        assert differential == expected
        assert image_rows(f) == wedge_rows(f)
    whole = tuple(range(n+1))
    top = (0,)*(n-1)
    assert image_rows(top) == simplex_atom(whole)
    bd = Counter()
    for f, a in boundary(top):
        for s in image_basis(f):
            bd[s] += a
    assert bd == simplex_d(whole)
    print(f'Rank {n}: all {3**(n-1)} suspended cube faces match the block atom tableaux.')
    if n != 6:
        return
    contexts, labels, full_labels = [], [], set()
    for i in range(1,n):
        face = tuple(1 if j==i else 0 for j in range(1,n))
        rows = image_rows(face)
        # Nonempty top row needs corrections at both strict ends of the whiskered atom.
        ends = [rows[:-2] + ((s,s),) for s in rows[-2]] if rows[-1][0] else [rows[:-1]]
        labels.extend(ends)
        allowed = {s for lo,hi in intervals(face) for size in range(1,5)
                   for s in combinations(range(lo,hi+1),size)}
        contexts.append(allowed)
        cells = close_atoms(map(simplex_atom, allowed), 3)
        full = {q for q in cells if {v for pair in q for side in pair for s in side for v in s} == set(whole)}
        full_labels.update(full)
        assert all({s for s in support(q) if len(s)<=4} <= allowed for q in ends)
        print(f'  cut {i}: {len(ends)} comparison labels, top four-cells '
              f'{[len(q[-1][0]) for q in ends]}, three-skeleton '
              f'{[sum(len(s)==j for s in allowed) for j in range(1,5)]}, '
              f'{len(full)} full labels among {len(cells)} three-cells')
    assert len(set(labels)) == 7
    union = set.union(*contexts)
    assert union == {s for size in range(1,5) for s in combinations(whole,size)
                     if not {0,n} <= set(s)}
    print(f'Seven distinct strict labels; union of the five three-skeleta has {len(union)} generators.')
    heights = Counter(max(j for j, row in enumerate(q) if any(row)) for q in full_labels)
    assert heights == {1: 1, 2: 89, 3: 206}
    print(f'Distinct full three-labels by underlying dimension: {dict(sorted(heights.items()))}')


if __name__ == '__main__':
    for n in range(2,8):
        census(n)
