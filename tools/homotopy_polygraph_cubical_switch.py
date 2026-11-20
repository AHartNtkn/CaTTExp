"""Compute every cube-chain hom of the cubical switch in HPOL r5, Response 3."""

from collections import Counter, defaultdict
from functools import cache


def subsets(mask):
    part = mask
    while part:
        yield part
        part = (part - 1) & mask
    yield 0


def cube_chain_betti(chains, weight):
    if not chains:
        return ()
    counts = Counter()
    ranks = Counter()
    basis = {}
    index = {chain: i for i, chain in enumerate(chains)}
    for chain in chains:
        degree = weight - len(chain)
        counts[degree] += 1
        column = 0
        for i, bead in enumerate(chain):
            for first in subsets(bead):
                if first and first != bead:
                    face = chain[:i] + (first, bead ^ first) + chain[i + 1:]
                    column ^= 1 << index[face]
        while column:
            pivot = column.bit_length()
            if pivot not in basis:
                basis[pivot] = column
                ranks[degree] += 1
                break
            column ^= basis[pivot]
    betti = [counts[k] - ranks[k] - ranks[k + 1] for k in range(max(counts) + 1)]
    while betti and not betti[-1]:
        betti.pop()
    return tuple(betti)


def verify(name, rows, facets, expected):
    all_rows = (1 << rows) - 1
    all_facets = (1 << len(facets)) - 1
    switch = 1 << (rows + len(facets))
    full = 2 * switch - 1

    def parts(state):
        return state & all_rows, all_facets ^ ((state >> rows) & all_facets)

    def incident(i, j):
        return all(i & ~facet == 0 for k, facet in enumerate(facets) if j & (1 << k))

    def allowed(state):
        i, j = parts(state)
        if state & switch:
            column_face = any(incident(1 << k, j) for k in range(rows))
            return column_face and (j != 0 or i == all_rows)
        return any(i & ~f == 0 for f in facets) and (i != 0 or j == all_facets)

    vertices = {s for s in range(full + 1) if allowed(s)}
    outgoing = defaultdict(list)
    for start in vertices:
        for step in subsets(full ^ start):
            if not step:
                continue
            corners = [start | v for v in subsets(step)]
            if not all(v in vertices for v in corners):
                continue
            if step & switch:
                labels = [parts(v) for v in corners]
                if not all(i and j and incident(i, j) for i, j in labels):
                    continue
            outgoing[start].append(step)

    @cache
    def histories(start, end):
        if start == end:
            return ((),)
        return tuple((step,) + tail for step in outgoing[start] if step & ~end == 0
                     for tail in histories(start | step, end))

    reachable = exceptional = largest = 0
    for start in vertices:
        for end in vertices:
            if start & ~end:
                continue
            chains = histories(start, end)
            actual = cube_chain_betti(chains, (end ^ start).bit_count())
            if start & switch == 0 and end & switch:
                i0, j0 = parts(start)
                i1, j1 = parts(end)
                crosses = any(i and i0 & ~i == 0 and j and j1 & ~j == 0 and incident(i, j)
                              for i in subsets(i1) for j in subsets(j0))
                assert bool(chains) == crosses
            else:
                assert chains
            if chains:
                reachable += 1
                largest = max(largest, len(chains))
                assert actual == (expected if (start, end) == (0, full) else (1,))
                exceptional += actual != (1,)
    print(f'{name}: {len(vertices)} states, {reachable} reachable endpoint pairs, '
          f'{exceptional} with positive Betti number; up to {largest} cube chains')


def section_cells(rows, facets):
    """List cubical cells from the two extreme subsets, independently of histories."""
    cells = defaultdict(list)
    for i_max in range(1, 1 << rows):
        neighbors = sum(1 << k for k, f in enumerate(facets) if i_max & ~f == 0)
        for j_max in subsets(neighbors):
            for i_min in subsets(i_max):
                for j_min in subsets(j_max):
                    if i_min and j_min:
                        low = i_min | (j_min << rows)
                        high = i_max | (j_max << rows)
                        cells[(high ^ low).bit_count()].append((low, high))
    return cells


def section_betti(cells, prime):
    ranks = Counter()
    for degree in range(1, max(cells) + 1):
        indices = {face: i for i, face in enumerate(cells[degree - 1])}
        basis = {}
        for low, high in cells[degree]:
            axes = high ^ low
            sign = 1
            column = {}
            while axes:
                axis = axes & -axes
                axes ^= axis
                column[indices[low | axis, high]] = sign % prime
                column[indices[low, high ^ axis]] = -sign % prime
                sign *= -1
            while column:
                pivot = max(column)
                if pivot not in basis:
                    scale = pow(column[pivot], -1, prime)
                    basis[pivot] = {i: v * scale % prime for i, v in column.items()}
                    ranks[degree] += 1
                    break
                scale = column[pivot]
                for i, v in basis[pivot].items():
                    coefficient = (column.get(i, 0) - scale * v) % prime
                    if coefficient:
                        column[i] = coefficient
                    else:
                        column.pop(i, None)
    result = [len(cells[k]) - ranks[k] - ranks[k + 1] for k in range(max(cells) + 1)]
    while result and not result[-1]:
        result.pop()
    return tuple(result)


def check_projective_plane():
    triangles = ('123', '124', '135', '146', '156', '236', '245', '256', '345', '346')
    facets = [sum(1 << (int(v) - 1) for v in t) for t in triangles]
    cells = section_cells(6, facets)
    assert section_betti(cells, 2) == (1, 1, 1)
    assert section_betti(cells, 3) == (1,)
    print(f'Projective plane: {sum(map(len, cells.values()))} switch cells, '
          'Betti (1, 1, 1) mod 2 and (1) mod 3.')


if __name__ == '__main__':
    verify('triangle boundary', 3, [0b011, 0b110, 0b101], (1, 1))
    verify('filled triangle', 3, [0b111], (1,))
    verify('path', 3, [0b011, 0b110], (1,))
    check_projective_plane()
