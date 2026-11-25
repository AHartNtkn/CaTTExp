"""Cellular chains of cyclic covers for two gap scalars and a straddling interval."""

from itertools import combinations, permutations


def splits(items):
    for size in range(1, len(items)):
        for left in combinations(items, size):
            yield left, tuple(i for i in items if i not in left)


def partitions(items):
    yield (items,)
    for first, tail in splits(items):
        for rest in partitions(tail):
            yield (first,) + rest


# The rod has name 0. Names 1 and 2 are portless points at the interior gap.
# Within a temporal block a planar tier is an x-ordered tuple.
def charts(block):
    for rows in partitions(block):
        if any(0 in row and len(row) > 1 for row in rows):
            continue
        def ordered(i):
            if i == len(rows):
                yield ()
                return
            for row in permutations(rows[i]):
                for rest in ordered(i+1):
                    yield (row,) + rest
        yield from ordered(0)


def cells(blocks):
    if not blocks:
        yield ()
        return
    for first in charts(blocks[0]):
        for rest in cells(blocks[1:]):
            yield (first,) + rest


def members(chart):
    return sorted(i for row in chart for i in row)


def restrict(chart, subset):
    rows = [tuple(i for i in row if i in subset) for row in chart]
    return tuple(row for row in rows if row)


def dimension(cell):
    return sum(2*len(members(chart)) - 1 - len(chart) for chart in cell)


def sheet_change(chart, new_order):
    """Transport from a block's increasing serial vertex to the chosen facet."""
    order = members(chart)
    height = {i: h for h, row in enumerate(chart) for i in row}
    delta = 0
    for target, event in enumerate(new_order):
        pos = order.index(event)
        while pos > target:
            a, b = order[pos-1:pos+1]
            if 0 in (a, b):
                scalar = a or b
                crossing = 1 if height[a] < height[b] else -1
                inversion_change = 1 if a == 0 else -1
                turn = (crossing - inversion_change) // 2
                delta += turn if scalar == 2 else -turn
            order[pos-1:pos+1] = b, a
            pos -= 1
    return delta


def boundary(cell):
    for k, chart in enumerate(cell):
        def replace(new):
            return cell[:k] + new + cell[k+1:]
        for h, row in enumerate(chart):
            for left, right in splits(row):
                refined = chart[:h] + (left, right) + chart[h+1:]
                yield replace((refined,)), 0
        for left, right in splits(members(chart)):
            face = replace((restrict(chart, left), restrict(chart, right)))
            # Splitting a horizontal tie across two temporal blocks collapses
            # its permutohedral factor; the image has codimension at least two.
            if dimension(face) == dimension(cell) - 1:
                yield face, sheet_change(chart, left + right)


def extend_basis(basis, columns):
    for col in columns:
        while col:
            pivot = col.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = col
                break
            col ^= basis[pivot]


def audit(sheets):
    by_dim = [[] for _ in range(4)]
    for blocks in partitions((0, 1, 2)):
        for cell in cells(blocks):
            by_dim[dimension(cell)].append(cell)
    address = [{c: i for i, c in enumerate(group)} for group in by_dim]
    matrices = [[]]
    bases = [{}]
    for d in range(1, 4):
        columns = []
        for cell in by_dim[d]:
            for sheet in range(sheets):
                col = 0
                for face, shift in boundary(cell):
                    j = address[d-1][face]*sheets + (sheet+shift) % sheets
                    col ^= 1 << j
                if d >= 2:
                    total = 0
                    for i, previous in enumerate(matrices[d-1]):
                        if col >> i & 1:
                            total ^= previous
                    assert total == 0
                columns.append(col)
        matrices.append(columns)
        basis = {}
        extend_basis(basis, columns)
        bases.append(basis)
    ranks = [len(basis) for basis in bases] + [0]
    betti = tuple(len(cells)*sheets-ranks[d]-ranks[d+1] for d, cells in enumerate(by_dim))
    assert betti == (1, 2, sheets+1, sheets)

    # With the rod first, the temporal scalar exchange times the two
    # different spatial tie orders gives the two hemispheres of one sphere.
    pair = [(((0,),), ((a, b),)) for a, b in ((1, 2), (2, 1))]
    sphere_basis = bases[3].copy()
    for sheet in range(sheets):
        i, j = (address[2][c]*sheets + sheet for c in pair)
        assert matrices[2][i] == matrices[2][j]
        extend_basis(sphere_basis, [(1 << i) ^ (1 << j)])
    assert len(sphere_basis) == ranks[3] + sheets
    print(sheets, 'sheets; cells', tuple(sheets*len(cs) for cs in by_dim),
          'Betti', betti, 'independent lifted spheres', sheets)


if __name__ == '__main__':
    for count in (1, 2, 3, 5, 8):
        audit(count)
