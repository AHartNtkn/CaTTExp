"""Finite witnesses for the universality responses on lax interchange, round 7."""

from itertools import product
from math import gcd


def check_square():
    # Paths in the directed square, encoded by their successive vertices.
    paths = {(v,) for v in range(4)}
    paths.update({(0, 1), (0, 2), (1, 3), (2, 3), (0, 1, 3), (0, 2, 3)})
    source, target = (0, 2, 3), (0, 1, 3)
    # A 2-cell consists of its two paths and its optional generator index.
    cells = {(path, path, None) for path in paths}
    cells.update((source, target, index) for index in range(2))

    def swap(cell):
        p, q, index = cell
        return p, q, None if index is None else 1 - index

    def join_labels(i, j):
        assert i is None or j is None
        return j if i is None else i

    def compose(f, g, cut):
        p, q, i = f
        r, s, j = g
        if cut == 0 and p[-1] == r[0]:
            return p + r[1:], q + s[1:], join_labels(i, j)
        if cut == 1 and q == r:
            return p, s, join_labels(i, j)
        return None

    count = 0
    for f, g, cut in product(cells, cells, range(2)):
        h = compose(f, g, cut)
        image = compose(swap(f), swap(g), cut)
        if h is None:
            assert image is None
        else:
            assert h in cells and image == swap(h)
            count += 1
    fillers = {f for f in cells if f[:2] == (source, target)}
    assert len(fillers) == 2 and all(swap(f) != f for f in fillers)
    assert all(swap(swap(f)) == f for f in cells)
    print(f"Square: {len(paths)} paths, {count} typed compositions, two exchanged fillers.")


def check_powers():
    # Left short hom is the one-object category C_q. The right arrow is
    # either an identity or the sole nonidentity arrow of [1].
    primes = (2, 3, 5, 7, 11, 13, 17, 19)
    cases = 0
    for q in primes:
        for p in primes:
            failures = []
            for a, b in product(range(q), range(2)):
                power, paste = 0, False
                for _ in range(p):
                    power = (power + a) % q
                    paste |= bool(a and b)
                direct = bool(power and b)
                if direct != paste:
                    failures.append((a, b))
                cases += 1
            expected = [(a, 1) for a in range(1, q)] if p == q else []
            assert failures == expected
        for a in range(q):
            for b, c in [(0, 0), (0, 1), (1, 0)]:
                assert bool(a and (b + c)) == (bool(a and b) or bool(a and c))
    print(f"Powers: {cases} assignments, diagonal failures only; all right splits hold.")


def check_cyclic_orders(limit):
    """Evaluate the split on powers and test the subgroup maps on the marked table."""
    primes = [p for p in range(2, limit + 1) if all(p % k for k in range(2, p))]
    spectra = {}
    assignments = 0
    for n in range(1, limit + 1):
        valid = set()
        for d, p in product(range(1, limit + 1), primes):
            failures = set()
            for a, proper in product(range(n), (False, True)):
                block = (a * d) % n
                total, expanded = 0, False
                for _ in range(p):
                    total = (total + block) % n
                    expanded |= bool(block and proper)
                direct = bool(total and proper)
                if direct != expanded:
                    failures.add((a, proper))
                assignments += 1
            # Multiplication by d has gcd(n,d) lifts of each point in its image.
            expected = gcd(n, d) * (gcd(n // gcd(n, d), p) - 1)
            assert len(failures) == expected
            if not failures:
                valid.add((d, p))
        spectra[n] = valid
    inclusions = 0
    for n, m in product(spectra, repeat=2):
        assert (spectra[n] <= spectra[m]) == (n % m == 0)
        if n % m:
            continue
        inc = [a * (n // m) for a in range(m)]
        assert len(set(inc)) == m
        for a, b in product(range(m), repeat=2):
            assert inc[(a + b) % m] == (inc[a] + inc[b]) % n
        for a, proper in product(range(m), (False, True)):
            assert bool(a and proper) == bool(inc[a] and proper)
        inclusions += 1
    print(f'Cyclic orders through {limit}: {assignments} split assignments, '
          f'{limit ** 2} ordered pairs, {inclusions} marked subgroup inclusions.')


if __name__ == '__main__':
    check_square()
    check_powers()
    check_cyclic_orders(32)
