"""Finite checks for the disk-tree rule and the signed guard models."""

from collections import Counter
from functools import lru_cache
from itertools import permutations, product

from interchange_pasting_minimum import face, globe, gray_layers, paste


def check_signed_strip():
    def disk(a, b):
        return a * b, -a * b, int((a, b) == (1, 1))

    def whisker(cell, pad):
        source, target, label = cell
        return source + pad, target + pad, label

    def then(f, g):
        assert f[1] == g[0]
        return f[0], g[1], f[2] + g[2]

    checks = 0
    for a, other, b in product(range(-3, 4), repeat=3):
        direct, left, right = (disk(v, b) for v in (a + other, a, other))
        # Insert each tile in its chronological 4-context on the strip.
        tiled = then(whisker(left, right[0]), whisker(right, left[1]))
        assert tiled[:2] == direct[:2]
        if not any(cell[0] for cell in (direct, left, right)):
            assert direct == tiled
        checks += 1
    assert [disk(a, 1) for a in (0, 1, -1)] == [(0, 0, 0), (1, -1, 1), (-1, 1, 0)]
    return checks


def check_disk_cocycles():
    # Evaluate actual Steiner faces and every matching paste, including
    # higher faces whose two routes carry the marked lower (2,2) atom.
    count = 0
    for p, q in ((2, 2), (3, 2), (2, 3)):
        left, right = globe(p, 1), globe(q, 1)
        weights = [(int(a[0] == b[0] == 2), (-2)**a[0] * 3**b[0])
                   for a, b in product(left, right)]

        @lru_cache(maxsize=None)
        def row(mask):
            return tuple(sum(w[i] for j, w in enumerate(weights) if mask >> j & 1)
                         for i in (0, 1))

        for cells in gray_layers(left, right):
            for cell in cells:
                for source, target in cell:
                    assert row(source) == row(target)
                for cut in range(len(cell) - 1):
                    for other in cells:
                        if face(cell, cut, 1) == face(other, cut, 0):
                            combined = paste(cell, other, cut)
                            assert row(combined[-1][0]) == tuple(
                                a + b for a, b in zip(row(cell[-1][0]), row(other[-1][0])))
                            count += 1
    return count


class Disk:
    """Sparse signed polynomial rows on an interval, and their top label."""

    def __init__(self, lo, hi, rows, label=0):
        self.lo, self.hi, self.rows, self.label = lo, hi, rows, label

    @property
    def rank(self):
        return len(self.rows) - 1

    def restricted(self, rank, lo, hi):
        if rank > self.rank:
            return {}
        return {powers: value for powers, value in self.rows[rank].items()
                if value and not any(powers[:lo] + powers[hi:])}

    def unmarked_weight(self, rank, marked):
        if rank > self.rank:
            return 0
        return sum(value for powers, value in self.rows[rank].items() if not powers[marked])


def leaf(dims, i, coeffs):
    rows = []
    for rank, coeff in enumerate(coeffs):
        powers = tuple(rank if j == i else 0 for j in range(len(dims)))
        rows.append({powers: coeff})
    return Disk(i, i + 1, rows)


def eligible(disk, dims):
    expected = tuple(d if disk.lo <= i < disk.hi else 0 for i, d in enumerate(dims))
    if not disk.rows[-1].get(expected):
        return False
    for lo in range(disk.lo, disk.hi):
        for hi in range(lo + 1, disk.hi + 1):
            for rank in range(1, min(2, sum(dims[lo:hi])) + 1):
                if not disk.restricted(rank, lo, hi):
                    return False
    return True


def tensor(x, y, dims, marked, exceptional):
    assert x.hi == y.lo
    rows = [Counter() for _ in range(x.rank + y.rank + 1)]
    for a, row_a in enumerate(x.rows):
        for b, row_b in enumerate(y.rows):
            for key, val in row_a.items():
                for other, coeff in row_b.items():
                    powers = tuple(i + j for i, j in zip(key, other))
                    rows[a + b][powers] += val * coeff
    tag = x.label * y.unmarked_weight(y.rank, marked) + x.unmarked_weight(x.rank, marked) * y.label
    if (x.lo, x.hi, y.hi) in exceptional and min(x.rank, y.rank) >= 2:
        unmarked_child = y if x.lo <= marked < x.hi else x
        if (eligible(x, dims) and eligible(y, dims)
                and all(unmarked_child.unmarked_weight(r, marked) > 0 for r in (1, 2))):
            tag += 1
    return Disk(x.lo, y.hi, rows, tag)


@lru_cache(maxsize=None)
def trees(lo, hi):
    if lo + 1 == hi:
        return (lo,)
    return tuple((x, y) for k in range(lo + 1, hi)
                 for x in trees(lo, k) for y in trees(k, hi))


def evaluate(tree, inputs, dims, marked, exceptional):
    if isinstance(tree, int):
        return inputs[tree]
    x, y = (evaluate(t, inputs, dims, marked, exceptional) for t in tree)
    return tensor(x, y, dims, marked, exceptional)


def path_nodes(tree, dims, marked):
    if isinstance(tree, int):
        return tree, tree + 1, set()
    lo, k, first = path_nodes(tree[0], dims, marked)
    _, hi, second = path_nodes(tree[1], dims, marked)
    bad = first | second
    if lo <= marked < hi and min(sum(dims[lo:k]), sum(dims[k:hi])) >= 2:
        bad.add((lo, k, hi))
    return lo, hi, bad


def check_trees():
    checked = failures = 0
    for dims in product(range(3), repeat=4):
        inputs = [leaf(dims, i, [1] * (d + 1)) for i, d in enumerate(dims)]
        for i, d in enumerate(dims):
            if not d:
                continue
            for tree in trees(0, len(dims)):
                _, _, bad = path_nodes(tree, dims, i)
                for node in bad or {None}:
                    cell = evaluate(tree, inputs, dims, i, {node})
                    assert cell.rows[-1] == {dims: 1}
                    assert cell.label == int(node is not None)
                    checked += 1
                    failures += cell.label
    return checked, failures


def check_rebracketing():
    count = differences = pseudo = 0
    for dims, marked in (((2, 1, 1), 0), ((2, 2, 2), 1), ((1, 1, 2), 2)):
        choices = []
        for j, d in enumerate(dims):
            # Signed cancellation is possible on the marked slot. Unsigned
            # rows of the others must have nonnegative, gapless support.
            allowed = tuple(product((-1, 0, 1), repeat=d)) if j == marked else (
                tuple(int(a < r) for a in range(d)) for r in range(d + 1))
            choices.append([leaf(dims, j, (1,) + coeffs) for coeffs in allowed])
        exceptions = {(0, 1, 3), (0, 2, 3)}
        for inputs in product(*choices):
            left, right = (evaluate(t, inputs, dims, marked, exceptions) for t in trees(0, 3))
            assert left.rows == right.rows
            if left.label != right.label:
                differences += 1
                for j, d in enumerate(dims):
                    if d >= 2:
                        assert inputs[j].restricted(2, j, j + 1)
                        assert all(x.restricted(1, x.lo, x.hi) for k, x in enumerate(inputs) if k != j)
            if dims == (2, 2, 2):
                mid = inputs[1]
                for r in (1, 2):
                    pair = tensor(inputs[0], Disk(1, 2, mid.rows[:r+1]), dims, marked, exceptions)
                    assert not pair.label and not pair.unmarked_weight(pair.rank, marked)
                if left.label == right.label == 1:
                    pseudo += 1
            count += 1
    assert differences and pseudo
    return count, differences, pseudo


def check_guard_boundaries():
    # A bracket can recover total mass from a crossing even though its
    # higher-rank input has zero mass. Its subinterval test must fail.
    dims = (3, 1, 2)
    x = leaf(dims, 0, (1, 1, 0, 1))
    y = leaf(dims, 1, (1, 1))
    z = leaf(dims, 2, (1, 1, 1))
    exceptions = {(0, 2, 3)}
    xy = tensor(x, y, dims, 0, exceptions)
    assert xy.rows[-1] == {(3, 1, 0): 1}
    assert xy.restricted(2, 0, 2) and not xy.restricted(2, 0, 1)
    assert not tensor(xy, z, dims, 0, exceptions).label

    # A positive existing tag on the preceding argument is allowed by the
    # model. It must also disappear in every pseudo test of the middle cell.
    dims = (2, 2, 2)
    y = leaf(dims, 0, (1, 1, 1, 1, 1))
    y.label = 5
    for rank in (1, 2):
        middle = leaf(dims, 1, (1,) * (rank + 1))
        pair = tensor(y, middle, dims, 1, {(0, 1, 3), (0, 2, 3)})
        assert not pair.label and not pair.unmarked_weight(pair.rank, 1)

    dims = (2, 1, 1)
    inputs = [leaf(dims, j, (1,) * (d + 1)) for j, d in enumerate(dims)]
    for tree, label in ((((0, 1), 2), 0), ((0, (1, 2)), 1)):
        assert evaluate(tree, inputs, dims, 0, {(0, 1, 3)}).label == label


def check_low_laws():
    count = 0
    for pad, edge, mass, moment in product(range(-2, 3), repeat=4):
        r, t = moment * edge, -moment * edge
        prefix, suffix = moment - pad * mass, moment + pad * mass
        square = (pad * edge) * mass
        assert prefix * edge + square == r and suffix * edge == r + square
        assert -suffix * edge + square == t and -prefix * edge == t + square
        count += 1
    def forward(n, k):
        return n + k

    def backward(n, k):
        return max(n - k, 0)

    for a, b, extra, point in product(range(-2, 3), range(4), range(4), range(8)):
        power = b * bool(a)
        assert backward(forward(point, power), power) == point
        assert backward(backward(point, power), extra * bool(a)) == backward(point, (b + extra) * bool(a))
        if power:
            assert forward(backward(0, power), power) != 0
        count += 1
    return count


def check_indexed_assignment():
    # Right regular action of S3, with multiplication composed in walking order.
    perms = tuple(permutations(range(3)))
    unit = perms[0]

    def mul(g, h):
        return tuple(h[i] for i in g)

    a, b = (1, 0, 2), (1, 2, 0)
    for g in perms:
        assert mul(mul(g, a), a) == mul(mul(mul(g, b), b), b) == g
        assert mul(mul(mul(mul(g, a), b), a), b) == g
    words = 0
    for length in range(9):
        for word in product((a, b), repeat=length):
            action = list(perms)
            for h in word:
                action = [mul(g, h) for g in action]
            assert len(set(action)) == 6
            advance = {g: int(g != unit) for g in perms}
            assert advance[unit] == 0
            assert int((advance[action[0]], 1) == (1, 1)) == int(action != list(perms))
            words += 1
    return words


if __name__ == '__main__':
    check_guard_boundaries()
    print("Signed strip assignments:", check_signed_strip())
    print("Signed low laws and one-sided join assignments:", check_low_laws())
    print("Matching Steiner pastes:", check_disk_cocycles())
    print("Principal trees (tests, positive countermodel labels):", check_trees())
    print("Triple assignments, unequal tags, double pseudo failures:", check_rebracketing())
    print("Regular-action words:", check_indexed_assignment())
