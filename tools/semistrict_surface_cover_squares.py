"""Compute Sq^2 on finite integral cycles and test Laurent Hopf attachments."""
from collections import Counter
from itertools import combinations, product


def disk_face(simplex, keep):
    """Restrict an ordered simplex of Sym^2(Delta[2]/boundary) joined to apices."""
    pair, apices = simplex
    size = len(pair[0])
    vertices = [j for j in keep if j < size]
    restricted = []
    for factor in pair:
        values = tuple(factor[j] for j in vertices)
        restricted.append(values if len(set(values)) == 3 else (-1,) * len(vertices))
    return tuple(sorted(restricted)), tuple(apices[j-size] for j in keep if j >= size)


def degenerate(simplex):
    (x, y), _ = simplex
    return any((x[i], y[i]) == (x[i+1], y[i+1]) for i in range(len(x)-1))


def dimension(simplex):
    pair, apices = simplex
    return len(pair[0]) + len(apices) - 1


def boundary(cycle):
    out = Counter()
    for simplex, n in cycle.items():
        indices = tuple(range(dimension(simplex) + 1))
        for j in indices:
            face = disk_face(simplex, indices[:j] + indices[j+1:])
            if not degenerate(face):
                out[face] += (-1)**j * n
    return {s: n for s, n in out.items() if n}


def projective_cycle(suspensions):
    # The product shuffle cycle descends with degree two through the symmetric square.
    chain = Counter()
    for left in combinations(range(1, 5), 2):
        right = tuple(i for i in range(1, 5) if i not in left)
        pair = tuple(sorted(tuple(sum(k <= j for k in cuts) for j in range(5))
                            for cuts in (left, right)))
        inversions = sum(x > y for x in left for y in right)
        chain[pair, ()] += (-1)**inversions
    assert len(chain) == 3 and all(abs(x) == 2 for x in chain.values())
    cycle = {s: n // 2 for s, n in chain.items()}
    for j in range(1, suspensions + 1):
        cycle = {(pair, apices + (sign*j,)): sign*n for (pair, apices), n in cycle.items()
                 for sign in (1, -1)}
    assert not boundary(cycle)
    return cycle


def bottom(simplex, suspensions):
    pair, apices = simplex
    return (apices == tuple(range(1, suspensions + 1))
            and sum(factor == (0, 1, 2) for factor in pair) % 2)


def square(simplex, suspensions):
    # For cup_(m-2) on an (m+2)-simplex the two deletion lists partition
    # four vertices, with two deletions for each m-face.
    indices = tuple(range(dimension(simplex) + 1))
    answer = 0
    for deleted in combinations(indices, 4):
        odd = {v for i, v in enumerate(deleted, 1) if (v+i) % 2}
        if len(odd) != 2:
            continue
        even = set(deleted) - odd
        left = disk_face(simplex, [j for j in indices if j not in odd])
        right = disk_face(simplex, [j for j in indices if j not in even])
        answer ^= bottom(left, suspensions) & bottom(right, suspensions)
    return answer


def strip_powers_of_t(poly):
    return poly // (poly & -poly) if poly else 0


def remainder(poly, divisor):
    # Binary digits are coefficients over F2. The Laurent variable is invertible.
    divisor = strip_powers_of_t(divisor)
    while divisor and poly.bit_length() >= divisor.bit_length():
        poly ^= divisor << (poly.bit_length() - divisor.bit_length())
    return poly


def finite_translates(poly, period):
    mask = (1 << period) - 1
    row = 0
    for i in range(poly.bit_length()):
        if (poly >> i) & 1:
            row ^= 1 << (i % period)
    pivots = {}
    for _ in range(period):
        v = row
        while v and v.bit_length() in pivots:
            v ^= pivots[v.bit_length()]
        if v:
            pivots[v.bit_length()] = v
        row = ((row << 1) & mask) | (row >> (period-1))
    return pivots


def audit():
    for k in range(5):
        chain = projective_cycle(k)
        assert sum(n*square(s, k) for s, n in chain.items()) % 2 == 1
        # Check the cochain on all (m+1)-faces of the actual support.
        for s in chain:
            n = dimension(s)
            for indices in combinations(range(n+1), n):
                f = disk_face(s, indices)
                assert sum(bottom(disk_face(f, [v for v in range(n) if v != j]), k)
                           for j in range(n)) % 2 == 0
    print('Integral cycles and dual Sq^2 readings checked on Sym^2(S^2) and four suspensions.')
    # An attachment along eta(a)+2b has no integral cellular top cycle.
    # Compute in <e,b | 2e=0, e+2b=0> using both integer relations.
    # The character e->2, b->1 to C4 detects e despite the mod-two top cycle.
    for e, b in product(range(-4, 5), repeat=2):
        in_lattice = b % 2 == 0 and (e - b//2) % 2 == 0
        assert in_lattice == ((2*e + b) % 4 == 0)
    print('The integral attaching lattice retains the nonzero Hopf value 2 in C4.')
    checks = 0
    # Every nonmonomial divisor used here divides t^period-1 after stripping
    # t powers. Choose such a period to compare Laurent membership with an
    # independent cyclic-sheet row reduction, including the zero ideal.
    for p, q in product(range(32), range(32)):
        period = next(n for n in range(6, 100) if not p or not remainder((1 << n) | 1, p))
        pivots = finite_translates(p, period)
        v = q
        while v and v.bit_length() in pivots:
            v ^= pivots[v.bit_length()]
        assert (v == 0) == (remainder(q, p) == 0)
        checks += 1
    print(f'{checks} Laurent attaching and test rows matched finite cyclic-sheet reductions.')


if __name__ == '__main__':
    audit()
