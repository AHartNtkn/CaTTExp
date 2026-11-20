"""Check rank shortcuts, parallel-face gates and compressed principal comparisons."""

from itertools import product

from check_interchange_uniform_space import verify_rows
from interchange_effective_rank import PrincipalWords, bridge_rank, column_ranks, principal_rank


def check_hemispheres():
    count = 0
    for p, q, right in product(range(3, 6), range(2, 6), (False, True)):
        def check(rank, table):
            nonlocal count
            for x, y in product(range(p + 2), range(q + 1)):
                limits = (y, x) if right else (x, y)
                # Under the two globe degeneracies exactly the basis factors
                # above the retained heights have zero chain image.
                height = next(j for j in reversed(range(len(table)))
                              if any(a[0] <= limits[0] and b[0] <= limits[1]
                                     for a, b in table[j][0]))
                assert 1 + height == bridge_rank(0, p, rank, 1 + x, 1 + y)
                count += 1
        verify_rows(p, q, right, check)
    return count


def gate(n, x, y):
    a, b = column_ranks(x, y, 3, n - 5)
    return principal_rank(n - 2, a, b)


def check_columns():
    for lo, length, x, y in product(range(7), range(8), range(12), range(12)):
        a, b = x, y
        for k in range(lo, lo + length):
            a, b = max(min(a, k + 1), b), max(a, min(b, k + 1))
        assert column_ranks(x, y, lo, length) == (a, b)
    n = 4 + 2**1024
    for x, y in product((3, 4, n-1, n), repeat=2):
        assert (gate(n, x, y) == n+1) == (x == n and y == n)


def block(mask):
    # Four outer crossings, two inner exchanges, and the temporal square.
    # Lower stationary pads can raise a nonfull intermediate rank up to
    # the preceding rank. They preserve each of the properness flags.
    arms = [principal_rank(0, 2 if mask & (1 << i) else 0,
                               2 if mask & (2 << i) else 0) for i in range(0, 8, 2)]
    early = max(3, principal_rank(1, *arms[:2]))
    late = max(3, principal_rank(1, *arms[2:]))
    return principal_rank(2, early, late)


def cover_cell(columns, masks, guard_mask):
    # Two universe elements, three candidate subsets. Each disjunction
    # combines three common-base inputs via structural products before lifting.
    guard = block(guard_mask)
    leaves = list(map(block, masks))
    rows = [gate(5, max([4] + [x for s, x in zip(columns, leaves) if s & bit]), guard)
            for bit in (1, 2)]
    combined = gate(6, *rows)
    truth6 = gate(5, guard, guard)
    return gate(7, combined, gate(6, truth6, truth6))


def check_covers():
    assert [i for i in range(256) if block(i) == 5] == [255]
    count = 0
    for columns in product(range(4), repeat=3):
        best = None
        for mask in range(8):
            items = [s for i, s in enumerate(columns) if mask & (1 << i)]
            covered = any(s & 1 for s in items) and any(s & 2 for s in items)
            if covered:
                cost = 8 * (1 + len(items))
                best = cost if best is None else min(cost, best)
        accepted = []
        for bits in product((0, 127, 255), repeat=4):
            if cover_cell(columns, bits[1:], bits[0]) == 8:
                accepted.append(sum(x.bit_count() for x in bits))
            count += 1
        assert min(accepted, default=None) == best
    return count


def check_words():
    w = PrincipalWords()
    # The weight-one 5-loops on the adjacent intervals of round 9 Response 2.
    x, y = w.seed('X'), w.seed('Y')
    binary = x
    for _ in range(100):
        binary = w.join(binary, binary)
    quaternary = x
    for _ in range(50):
        a = w.join(quaternary, quaternary)
        quaternary = w.join(w.join(a, quaternary), quaternary)
    a = w.tensor(binary, y)
    high = 4 + 2**256
    padded = w.tensor(w.elevate(quaternary, high), w.elevate(y, high))
    assert w.equal(w.elevate(a, padded.degree), padded)
    different = w.tensor(w.join(binary, x), y)
    assert not w.equal(a, different)
    # D has both 3-faces w, so every self-pair in this tower is typed.
    base = w.seed('D')
    tower = base
    observed = w.elevate(base, 6)
    for _ in range(256):
        tower = w.tensor(tower, tower)
        observed = w.tensor(observed, observed)
    assert tower.degree == tower.rank == high
    assert observed.degree == 4 + 2**257 and observed.rank == high
    assert w.equal(w.elevate(tower, observed.degree), observed)


if __name__ == '__main__':
    print(f'{check_hemispheres()} specialized bridge heights agree with projected signed tableaux.')
    check_columns()
    print('8064 column jumps match the expanded recurrence; gate flags agree at a 1025-bit degree.')
    print(f'{check_covers()} strand-retention cases agree with the least set-cover cost.')
    check_words()
    print('Compared 2^100 moving powers and a 256-level shared tensor tower, including elevated operands.')
