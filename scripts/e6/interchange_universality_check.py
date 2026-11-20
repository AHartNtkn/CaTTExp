"""Finite witnesses for Researcher Response 2 on lax interchange, round 7."""

from itertools import product


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


if __name__ == '__main__':
    check_square()
    check_powers()
