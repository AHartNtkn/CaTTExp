"""Check named meridian cablings, their Brunnian projections and the Hopf cross term."""

from collections import Counter
from itertools import permutations, product
from math import factorial, prod

from semistrict_surface_face_whitehead import evaluate, nested


def cable_and_project(terms, sizes):
    slots = [(colour, i) for colour, size in enumerate(sizes) for i in range(size)]
    projected = Counter()
    for mask in range(1 << len(slots)):
        kept = [slot for i, slot in enumerate(slots) if mask & (1 << i)]
        sign = (-1) ** (len(slots) - len(kept))
        blocks = [[slot for slot in kept if slot[0] == c] for c in range(len(sizes))]
        for word, coefficient in terms.items():
            for labelled in product(*(blocks[c] for c in word)):
                projected[labelled] += sign * coefficient
    return {word: value for word, value in projected.items() if value}


def check_polarizations():
    checks = 0
    for length in range(1, 6):
        for indices in product(range(3), repeat=length):
            _, terms = evaluate(nested(indices), range(3))
            sizes = [indices.count(c) for c in range(3)]
            result = cable_and_project(terms, sizes)
            folded = Counter()
            for word, value in result.items():
                assert len(set(word)) == length
                folded[tuple(c for c, _ in word)] += value
            factor = prod(map(factorial, sizes))
            assert dict(folded) == {word: factor * value for word, value in terms.items()}
            checks += 1
    return checks


def check_cyclic_action():
    # Extract coordinates at xyz and yxz from actual signed tensor expansions.
    bracket = [0, [1, 2]]
    basis = [evaluate(bracket, order)[1] for order in ('xyz', 'yzx', 'zxy')]
    assert not any(sum(p.get(w, 0) for p in basis) for w in permutations('xyz'))
    for a, b in product(range(-15, 16), repeat=2):
        if a == b == 0:
            continue
        coordinates = []
        for p, q in ((basis[0], basis[1]), (basis[1], basis[2])):
            coordinates.append([a * p.get(w, 0) + b * q.get(w, 0)
                                for w in (tuple('xyz'), tuple('yxz'))])
        (x, y), (z, w) = coordinates
        assert abs(x * w - y * z) == a*a - a*b + b*b


def determinant(rows):
    value = 0
    for order in permutations(range(len(rows))):
        inversions = sum(a > b for i, a in enumerate(order) for b in order[i+1:])
        value += (-1)**inversions * prod(row[j] for row, j in zip(rows, order))
    return value


def check_hopf_linking():
    # Fibres of S^3 -> CP^1 bound complex-line disks in B^4.
    # Signed intersection of distinct disks computes the off-diagonal cup entry.
    def frame(x, y):
        return [(1, 0, x, y), (0, 1, -y, x)]
    points = list(product(range(-2, 3), repeat=2))
    count = 0
    for (a, b), (x, y) in permutations(points, 2):
        intersection = determinant(frame(a, b) + frame(x, y))
        assert intersection == (x-a)**2 + (y-b)**2 and intersection > 0
        count += 1
    return count


if __name__ == '__main__':
    print(f'Checked {check_polarizations()} cabled brackets by alternating erasures and folding.')
    check_cyclic_action()
    print('Verified 960 orbit determinants in the four-particle test.')
    print(f'Checked {check_hopf_linking()} transverse Hopf fibre intersections, each of sign +1.')
