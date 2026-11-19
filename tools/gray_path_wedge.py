"""Check the two seam cuts for [r] ⊗ (P ∨ Q), for finite Batanin trees P,Q."""
import argparse
import json
from collections import Counter, defaultdict
from itertools import product

from gray_globe_comparison import atom, close_atoms
from gray_tree_section import generators, tree_boundary


def crossing_homs(cells, z, side):
    result = defaultdict(list)
    for x in cells:
        ((_, i), (address, a)), = x[0][0]
        ((_, j), (_, b)), = x[0][1]
        assert not address
        if side == 'left' and a < z == b:
            result[i, j, a].append(x)
        elif side == 'right' and a == z < b:
            result[i, j, b].append(x)
        elif side == 'whole' and a < z < b:
            result[i, j, a, b].append(x)
    return result


def times(chain, z):
    """Last move before the seam, first move beyond it (when present)."""
    left, right = [], []
    for (_, t), (segment, _) in chain:
        if segment:
            (left if segment[0] < z else right).append(t)
    return max(left, default=None), min(right, default=None)


def seam_path(i, j, z):
    return tuple((((t,), 0), ((), z)) for t in range(i, j))


def combine(left, right, i, j, z):
    seam = Counter(seam_path(i, j, z))
    rows = [(left[0][0], right[0][1])]
    for k, (l, r) in enumerate(zip(left[1:], right[1:]), 1):
        row = []
        for a, b in zip(l, r):
            chain = Counter(a + b)
            if k == 1:
                chain.subtract(seam)
            if any(n < 0 for n in chain.values()):
                return None
            row.append(tuple(sorted(chain.elements())))
        rows.append(tuple(row))
    return tuple(rows)


def path_identity(x, sign):
    c = x[1][sign]
    return (x[0], (c, c)) + (((), ()),) * (len(x) - 2)


def compose(x, y, cut):
    assert x[:cut] == y[:cut] and x[cut][1] == y[cut][0]
    return x[:cut] + ((x[cut][0], y[cut][1]),) + tuple(
        tuple(tuple(sorted(a + b)) for a, b in zip(s, t))
        for s, t in zip(x[cut + 1:], y[cut + 1:]))


def split(left, right, i, j, z, cut):
    vertex = ((((), cut), ((), z)),)

    def strip(x, suffix):
        rows = [(x[0][0], vertex) if suffix else (vertex, x[0][1])]
        pad = Counter(seam_path(cut, j, z) if suffix else seam_path(i, cut, z))
        row = []
        for chain in x[1]:
            counts = Counter(chain)
            counts.subtract(pad)
            assert all(n >= 0 for n in counts.values())
            row.append(tuple(sorted(counts.elements())))
        return tuple(rows) + (tuple(row),) + x[2:]

    return strip(left, True), strip(right, False)


def verify(r, p, q):
    if r < 0 or not p or not q:
        raise ValueError('use a nonnegative path length and two nonempty wedge components')
    clock = generators(tuple(() for _ in range(r)))
    z = len(p)
    left = generators(p)
    right = [((addr[0] + z,) + addr[1:], k) if addr else ((), k + z)
             for addr, k in generators(q)]

    def atoms(cells):
        return {atom(b, tree_boundary, len) for b in product(clock, cells)}

    left_atoms, right_atoms = atoms(left), atoms(right)
    whole_atoms = left_atoms | right_atoms
    totals = []
    for k in range(1, max(map(len, whole_atoms)) + 1):
        l_cells, r_cells = close_atoms(left_atoms, k), close_atoms(right_atoms, k)
        whole = crossing_homs(close_atoms(whole_atoms, k), z, 'whole')
        ls = crossing_homs(l_cells, z, 'left')
        rs = crossing_homs(r_cells, z, 'right')
        count = 0
        for (i, j, a, b), cells in whole.items():
            reconstructed = set()
            for left_cell, right_cell in product(ls[i, j, a], rs[i, j, b]):
                arrivals = [times(c, z)[0] for c in left_cell[1]]
                departures = [times(c, z)[1] for c in right_cell[1]]
                assert arrivals[0] <= arrivals[1] and departures[0] <= departures[1]
                h = combine(left_cell, right_cell, i, j, z)
                assert (h is not None) == all(x <= y for x, y in zip(arrivals, departures))
                if h is None:
                    continue
                assert h not in reconstructed
                reconstructed.add(h)
                if k == 1:
                    continue
                ly, rx = path_identity(left_cell, 0), path_identity(right_cell, 1)
                factors = []
                for x, y, cut in ((ly, right_cell, arrivals[0]), (left_cell, rx, departures[1])):
                    u, v = split(x, y, i, j, z, cut)
                    assert u in l_cells and v in r_cells
                    f = compose(u, v, 0)
                    assert f == combine(x, y, i, j, z)
                    factors.append(f)
                assert compose(*factors, 1) == h
            assert reconstructed == set(cells)
            count += len(cells)
        totals.append(count)
    return totals


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('r', type=int)
    parser.add_argument('p', type=json.loads)
    parser.add_argument('q', type=json.loads)
    args = parser.parse_args()
    print('Crossing cells checked by dimension:', *verify(args.r, args.p, args.q))
