"""Check stationary packet maps and exact-support decompositions of deck spheres."""
from collections import Counter
from itertools import combinations, product

from semistrict_surface_deck_ideals import collect, erase, multiply
from semistrict_surface_gate_forests import cable
from semistrict_surface_mixed_word_tests import point_push, read_push
from semistrict_surface_shared_edge import braid_image


def subsets(row):
    return (s for k in range(len(row) + 1) for s in combinations(row, k))


def project(poly, keep, row):
    for i in row:
        forgotten = erase(poly, i)
        if i in keep:
            poly = collect([*poly.items(), *((w, -n) for w, n in forgotten.items())])
        else:
            poly = forgotten
    return poly


def augmentation_monomial(row):
    poly = {(): 1}
    for i in row:
        poly = multiply(poly, {(i,): 1, (): -1})
    return poly


def packet_checks():
    maps = 0
    for h in range(1, 8):
        for chosen in subsets(tuple(range(1, h + 1))):
            k = len(chosen)
            movie = cable(point_push((-1,)), [1, k])
            assert read_push(k, movie) == tuple(-i for i in range(1, k + 1))
            # Move the last active slot first, without crossing another active slot.
            # braid_image composes automorphisms from right to left.
            steps = [i for j in reversed(range(k)) for i in range(j + 1, chosen[j])]
            images = braid_image(h, tuple(-i for i in reversed(steps)))
            assert images[:k] == tuple((i,) for i in chosen)
            maps += 1
    return maps


def projection_checks():
    row = tuple(range(1, 7))
    polynomials = [collect((s, (-2)**len(s) + sum(s)) for s in subsets(row)),
                   {(-6, 2, -3, -2, 6): -5, (1, -4, 6, 4): 2, (): 7}]
    for poly in polynomials:
        parts = [project(poly, s, row) for s in subsets(row)]
        assert collect(term for part in parts for term in part.items()) == poly
        for s, part in zip(subsets(row), parts, strict=True):
            assert all(not erase(part, i) for i in s)
            assert all(set(map(abs, w)) <= set(s) for w in part)
            if poly is polynomials[0]:
                # Independent expansion of the old words x_i = 1 + u_i.
                coefficient = sum(n for w, n in poly.items() if set(s) <= set(w))
                assert part == collect((w, coefficient * a) for w, a in augmentation_monomial(s).items())
    return len(parts) * len(polynomials)


def quotient_product(left, right, exterior):
    """Multiply in the signed exterior quotient or the group ring of the bit vectors."""
    result = Counter()
    for s, a in left.items():
        for t, b in right.items():
            if exterior:
                if s & t:
                    continue
                inversions = sum((t & ((1 << j) - 1)).bit_count()
                                 for j in range(s.bit_length()) if s & (1 << j))
                result[s | t] += (-1)**inversions * a * b
            else:
                result[s ^ t] += a * b
    return normalize(result, exterior)


def normalize(poly, exterior):
    values = {s: n % 2 if exterior and s.bit_count() >= 3 else n for s, n in poly.items()}
    return {s: n for s, n in values.items() if n}


def evaluate(word, exterior):
    result = {0: 1}
    for letter in word:
        bit = 1 << (abs(letter) - 1)
        generator = {0: 1, bit: 1 if letter > 0 else -1} if exterior else {bit: 1}
        result = quotient_product(result, generator, exterior)
    return result


def quadratic_checks():
    words = 0
    for size in range(5):
        for w in product((-3, -2, -1, 1, 2, 3), repeat=size):
            involution = evaluate(w, False)
            assert quotient_product(involution, involution, False) == {0: 1}
            diff = Counter(evaluate(w, True))
            diff[0] -= 1
            assert not quotient_product(diff, diff, True)
            words += 1
    assert quotient_product({2: 1}, {1: 1}, True) == {3: -1}
    assert quotient_product({3: 1}, {4: 1}, True) == {7: 1}
    assert not quotient_product({3: 2}, {4: 1}, True)
    return words


if __name__ == '__main__':
    print(f'{packet_checks()} stationary packet placements matched the meridian maps.')
    print(f'{projection_checks()} support components reconstructed two free-group polynomials.')
    print(f'{quadratic_checks()} signed deck words satisfied both universal quadratic tests.')
