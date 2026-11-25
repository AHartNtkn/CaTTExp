"""Check the five-name rational test and isolate degree-nine torsion on pure 3-scalars."""

from argparse import ArgumentParser
from collections import Counter
from itertools import permutations, product

from semistrict_surface_face_whitehead import evaluate
from semistrict_surface_meridian_polarization import cable_and_project


def commutator(letters):
    tree = letters[-1]
    for letter in reversed(letters[:-1]):
        tree = [letter, tree]
    return tree


def quartic_characters():
    slots = [order + (3,) for order in permutations(range(3))]
    permutations4 = tuple(permutations(range(4)))
    classes = Counter()
    for odd in (False, True):
        for perm in permutations4:
            fixed = sum(i == j for i, j in enumerate(perm))
            inversions = sum(i > j for k, i in enumerate(perm) for j in perm[k+1:])
            sign = (-1)**inversions
            trace = 0
            for order in slots:
                image = evaluate(commutator(order), perm, odd_letters=odd)[1]
                coordinates = [image.get(word, 0) for word in slots]
                reconstructed = Counter()
                for coefficient, basis in zip(coordinates, slots, strict=True):
                    terms = evaluate(commutator(basis), range(4), odd_letters=odd)[1]
                    reconstructed.update({w: coefficient*n for w, n in terms.items()})
                assert all(image.get(w, 0) == reconstructed[w] for w in permutations4)
                trace += image.get(order, 0)
            assert trace == (fixed - 1)*(1 + sign)
            if odd:
                classes[trace] += 1
    return classes


def binary_route(pair, xx_y, yy_x):
    """Read (pair eta^2, [x,[x,y]] eta, [y,[y,x]] eta) in a two-hole fibre."""
    if not (xx_y % 2 or yy_x % 2):
        return 'pair eta^2' if pair % 2 else 'zero'
    repeated = 0 if xx_y % 2 else 1
    sizes = (2, 1) if repeated == 0 else (1, 2)
    terms = Counter()
    for coeff, tree in ((xx_y, [0, [0, 1]]), (yy_x, [1, [1, 0]])):
        terms.update({word: coeff*n for word, n in evaluate(tree, range(2))[1].items()})
    projection = cable_and_project(terms, sizes)
    # The pair carries eta^2, a suspension. Its linear cabling has no three-name part.
    assert not cable_and_project(evaluate([0, 1], range(2))[1], sizes)
    target = ((1-repeated, 0), (repeated, 0), (repeated, 1))
    jacobi_term = evaluate([0, [1, 2]], target)[1]
    assert {w for w, n in projection.items() if n % 2} == {w for w, n in jacobi_term.items() if n % 2}
    return f'cable {"xy"[repeated]} twice, then take the triple eta test'


def check_ternary():
    words = tuple(permutations('xyz'))
    cycle = [evaluate([0, [1, 2]], order)[1] for order in ('xyz', 'yzx', 'zxy')]
    for a, b in ((1, 0), (0, 1), (1, 1)):
        orbit = []
        for i in range(3):
            left, right = cycle[i], cycle[(i+1) % 3]
            orbit.append(tuple((a*left.get(w, 0) + b*right.get(w, 0)) % 2 for w in words))
        assert len(set(orbit)) == 3 and tuple(cycle[0].get(w, 0) % 2 for w in words) in orbit


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--two-hole', nargs=3, type=int, metavar=('PAIR', 'XXY', 'YYX'))
    args = parser.parse_args()
    if args.two_hole:
        print(binary_route(*args.two_hole))
    else:
        print('All 48 stationary permutation actions have character standard plus signed standard.')
        traces = quartic_characters()
        assert traces == {6: 1, -2: 3, 0: 20}
        print(f'Traces with multiplicities {dict(sorted(traces.items()))}.')
        for pair, a, b in product(range(2), repeat=3):
            route = binary_route(pair, a, b)
            assert (route == 'zero') == (not any((pair, a, b)))
        check_ternary()
        print('Separated all eight two-hole torsion coordinates and all three nonzero ternary vectors.')
