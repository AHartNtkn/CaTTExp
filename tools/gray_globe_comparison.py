"""Check the strict comparison for two globes. Run with e.g. arguments 3 3."""
import argparse
from collections import Counter, defaultdict, deque
from functools import cache
from itertools import product


def globe(dim):
    # Tags 0 and 1 are the two parallel faces; tag 2 is the top generator.
    return [(k, tag) for k in range(dim + 1)
            for tag in ((0, 1) if k < dim else (2,))]


def boundary(basis):
    differential = Counter()
    sign = 1
    for j, (degree, _) in enumerate(basis):
        if degree:
            for side, coefficient in ((0, -1), (1, 1)):
                face = basis[:j] + ((degree - 1, side),) + basis[j + 1:]
                differential[face] += sign * coefficient
        sign *= (-1) ** degree
    return differential


@cache
def atom(basis):
    degree = sum(dim for dim, _ in basis)
    hemispheres = []
    for sign in (-1, 1):
        chain = Counter([basis])
        rows = [(basis,)]
        for _ in range(degree):
            differential = Counter()
            for generator, multiplicity in chain.items():
                for face, coefficient in boundary(generator).items():
                    differential[face] += sign * multiplicity * coefficient
            chain = +differential
            rows.append(tuple(sorted(chain.elements())))
        hemispheres.append(rows[::-1])
    return tuple(zip(*hemispheres))


def strict_cells(shape, degree):
    """Generate a fixed level from all padded atoms and their strict composites."""
    empty_row = ((), ())
    cells = set()
    for basis in product(*(globe(dim) for dim in shape)):
        rows = atom(basis)
        if len(rows) <= degree + 1:
            cells.add(rows + (empty_row,) * (degree + 1 - len(rows)))
    pending = deque(cells)
    by_source, by_target = defaultdict(list), defaultdict(list)

    def compose(x, y, k):
        upper = tuple(tuple(tuple(sorted(a + b)) for a, b in zip(row, col))
                      for row, col in zip(x[k + 1:], y[k + 1:]))
        composite = x[:k] + ((x[k][0], y[k][1]),) + upper
        if composite not in cells:
            cells.add(composite)
            pending.append(composite)

    while pending:
        x = pending.popleft()
        for k in range(degree):
            if all(row == empty_row for row in x[k + 1:]):
                continue  # composing a unit at k yields its other argument
            source = (x[:k], x[k][0])
            target = (x[:k], x[k][1])
            for left in by_target[source]:
                compose(left, x, k)
            for right in by_source[target]:
                compose(x, right, k)
            by_source[source].append(x)
            by_target[target].append(x)
    return cells


def suspend(cell):
    return (cell[0] + 1, cell[1])


def image_basis(basis):
    p, middle, q = basis
    if middle[0]:
        return [(suspend(p), suspend(q))]
    side = middle[1]
    result = []
    if q[0] == 0:
        result.append((suspend(p), (0, 1 - side)))
    if p[0] == 0:
        result.append(((0, side), suspend(q)))
    return result


CORNERS = tuple((((0, side), (0, side)),) for side in (0, 1))


@cache
def image(tableau):
    def chain_image(chain):
        return tuple(sorted(y for x in chain for y in image_basis(x)))
    return (CORNERS,) + tuple((chain_image(s), chain_image(t)) for s, t in tableau)


def face(tableau, side):
    boundary_chain = tableau[-2][side]
    return tableau[:-2] + ((boundary_chain, boundary_chain),)


def verify(m, n):
    if min(m, n) < 1:
        raise ValueError('both suspended globes must have positive dimension')
    lifts = {}
    for p, q in product(globe(m - 1), globe(n - 1)):
        x = atom((p, (1, 2), q))
        assert image(x) == atom((suspend(p), suspend(q)))
        pending = [x]
        while pending:
            x = pending.pop()
            y = image(x)
            if y in lifts:
                assert lifts[y] == x
                continue
            lifts[y] = x
            if len(x) > 1:
                pending.extend(face(x, side) for side in (0, 1))

    print('hom degree | source cells | diagonal hom cells')
    for k in range(m + n):
        source = strict_cells((m - 1, 1, n - 1), k)
        target = {y for y in strict_cells((m, n), k + 1) if y[0] == CORNERS}
        fibres = defaultdict(list)
        for x in source:
            fibres[image(x)].append(x)
        assert fibres.keys() == target
        for y in target:
            if y not in lifts:
                compatible = [x for x in fibres[y] if bool(x[-1][0]) == bool(y[-1][0])
                              and (not k or all(face(x, d) == lifts[face(y, d)] for d in (0, 1)))]
                assert compatible, ('no lift with the selected faces', k, y)
                lifts[y] = min(compatible)
            x = lifts[y]
            assert x in source and image(x) == y
            assert bool(x[-1][0]) == bool(y[-1][0])
            if k:
                assert all(face(x, d) == lifts[face(y, d)] for d in (0, 1))
        print(k, len(source), len(target), sep=' | ')
    return lifts


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    args = parser.parse_args()
    verify(args.m, args.n)
