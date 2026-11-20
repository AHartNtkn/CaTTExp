"""Exhaust the signed Gray tables for unary subdivisions in both tensor orders."""

from collections import Counter, defaultdict
from itertools import product


def globe(degree, pieces):
    """The directed complex of a stack of top globes joined at codimension one."""
    differential = {}
    for d in range(degree + 1):
        count = pieces if d == degree else pieces + 1 if d + 1 == degree else 2
        for i in range(count):
            lo = i if d == degree else 0
            differential[d, i] = {(d - 1, lo): -1, (d - 1, lo + 1): 1} if d else {}
    return differential


def tensor_atoms(left, right):
    basis = list(product(left, right))
    index = {b: i for i, b in enumerate(basis)}
    differential = []
    for a, b in basis:
        row = {index[x, b]: c for x, c in left[a].items()}
        row.update({index[a, x]: (-1)**a[0] * c for x, c in right[b].items()})
        differential.append(row)

    def hemisphere(mask, sign):
        row = Counter()
        for j, boundary in enumerate(differential):
            if mask & (1 << j):
                row.update(boundary)
        return sum(1 << j for j, c in row.items() if c * sign > 0)

    atoms = defaultdict(set)
    for i, (a, b) in enumerate(basis):
        degree = a[0] + b[0]
        rows = [(1 << i, 1 << i)]
        for _ in range(degree):
            source, target = rows[-1]
            rows.append((hemisphere(source, -1), hemisphere(target, 1)))
        atoms[degree].add(tuple(reversed(rows)))
    return atoms


def face(cell, cut, side):
    row = cell[cut][side]
    return cell[:cut] + ((row, row),)


def paste(left, right, cut):
    rows = list(left[:cut]) + [(left[cut][0], right[cut][1])]
    for (a, b), (c, d) in zip(left[cut+1:], right[cut+1:]):
        assert not (a & c or b & d), "non-squarefree composite"
        rows.append((a | c, b | d))
    return tuple(rows)


def gray_layers(left, right):
    atoms = tensor_atoms(left, right)
    layers = []
    for degree, generators in sorted(atoms.items()):
        cells = generators.copy()
        if degree:
            cells.update(c + ((0, 0),) for c in layers[-1])
        while True:
            size = len(cells)
            for cut in range(degree):
                starts = defaultdict(list)
                for cell in cells:
                    starts[face(cell, cut, 0)].append(cell)
                cells.update({paste(x, y, cut) for x in cells for y in starts[face(x, cut, 1)]})
            if len(cells) == size:
                break
        layers.append(cells)
    return layers


def check_table(left, right):
    layers = gray_layers(left, right)
    matches = 0
    for degree, cells in enumerate(layers):
        proper = [c for c in cells if c[-1][0]]
        for cut in range(degree - 1):
            # Test a partner of the smallest active rank at this cut.
            partners = [c for c in (cells if cut + 2 == degree else layers[cut+2]) if c[-1][0]]
            starts = {face(c, cut, 0) for c in partners}
            ends = {face(c, cut, 1) for c in partners}
            for c in proper:
                assert face(c, cut, 1) not in starts and face(c, cut, 0) not in ends
                matches += 2 * len(partners)
    return sum(map(len, layers)), matches


if __name__ == "__main__":
    table_count = cells = matches = 0
    for p in range(2, 7):
        for moving, stationary in ((globe(p, 1), globe(1, 2)), (globe(p, 2), globe(1, 1))):
            for left, right in ((moving, stationary), (stationary, moving)):
                count, tested = check_table(left, right)
                cells += count
                matches += tested
                table_count += 1
    print(f"{table_count} unary subdivision tables, {cells} tableau entries, {matches} oriented partner tests.")

    strip = gray_layers(globe(2, 2), globe(2, 1))
    assert [len(level) for level in strip] == [4, 26, 98, 139, 146]
    for cut in range(3):
        partners = [c for level in strip[cut + 2:] for c in level if c[-1][0]]
        starts = {face(c, cut, 0) for c in partners}
        ends = {face(c, cut, 1) for c in partners}
        for degree in range(cut + 2, len(strip)):
            active = [c for c in strip[degree] if c[-1][0] and
                      (face(c, cut, 1) in starts or face(c, cut, 0) in ends)]
            assert len(active) == (8 if (cut, degree) == (0, 2) else 0)
    print("Two-tile strip: only hom-rank 2 admits proper inner partners, all at cut 0.")
