"""Finite tables used in the weak-initiality obstruction (round 7, Response 3)."""

from collections import Counter
from itertools import combinations_with_replacement, product

from interchange_quotient_fibers import check_subdivisions, partitions, tensor_rows


def marked_disk(lo, hi, right):
    top_row = tensor_rows((lo, hi), right)[4, 0]
    return top_row, hi - lo == 2 and right == (0, 1)


def check_strip():
    assert check_subdivisions(2, 1) == 2
    whole = tensor_rows((0, 2), (0, 1))
    direct, subdivided = sorted(partitions(2), key=len)
    for strip in (direct, subdivided):
        row = Counter()
        bit = False
        for lo, hi in strip:
            tile, mark = marked_disk(lo, hi, (0, 1))
            row.update(tile)
            bit |= mark
        assert row == whole[4, 0]
        assert bit == (strip == direct)

    # Tag a W just when its left advance traverses both edges.
    cells = []
    for lo in range(3):
        for hi in range(lo, 3):
            for right_span in combinations_with_replacement(range(2), 2):
                row, mark = marked_disk(lo, hi, right_span)
                assert row or not mark
                cells.extend((row, bit) for bit in ((False, True) if row else (False,)))
    for a, b in product(cells, repeat=2):
        row, bit = a[0] + b[0], a[1] or b[1]
        assert row or not bit
    print("Strip: two typed subdivisions, identical signed tableau, distinct Boolean tags.")


def multiply(a, b):
    # The nonunit left-zero semigroup with an identity adjoined.
    return a if a != '1' else b


def compose(first, second):
    assert first[1] == second[0]
    return first[0], second[1]


def multiply_arrows(left, right):
    return multiply(left[0], right[0]), multiply(left[1], right[1])


def comparison_faces(active_left, active_right):
    x, y = ('x', 'y') if active_left and active_right else ('1', '1')
    return multiply(y, x), multiply(x, y)


def check_comparison():
    monoid = ('1', 'x', 'y')
    for a, b, c in product(monoid, repeat=3):
        assert multiply(a, '1') == multiply('1', a) == a
        assert multiply(multiply(a, b), c) == multiply(a, multiply(b, c))

    # Codiscrete arrows are pairs of endpoints. Check all two-variable
    # functorial pastes induced by multiplication on this groupoid.
    for a, b, c, d, e, f in product(monoid, repeat=6):
        left = compose((a, b), (b, c))
        right = compose((d, e), (e, f))
        first = multiply_arrows((a, b), (d, e))
        second = multiply_arrows((b, c), (e, f))
        assert compose(first, second) == multiply_arrows(left, right)

    for active_left, active_right in product((False, True), repeat=2):
        active = active_left and active_right
        source, target = comparison_faces(active_left, active_right)
        assert (source == target) == (not active)
        assert source == target or (source, target) == ('y', 'x')
    print("High comparison: associative three-element monoid, 729 functorial pastes, four guard cases.")


def check_guarded_split():
    failures = []
    cases = 0
    for lo, mid, hi in combinations_with_replacement(range(3), 3):
        for right_span in combinations_with_replacement(range(2), 2):
            cases += 1
            intervals = [(lo, hi), (lo, mid), (mid, hi)]
            whole, left, right = [marked_disk(a, b, right_span) for a, b in intervals]
            assert whole[0] == left[0] + right[0]
            matches = whole[1] == (left[1] or right[1])
            if not matches:
                failures.append((lo, mid, hi, right_span))
            tests = [comparison_faces(a < b, right_span[0] < right_span[1]) for a, b in intervals]
            if all(source == target for source, target in tests):
                assert matches
    assert failures == [(0, 1, 2, (0, 1))]
    print(f"Strip: the guarded split holds on all {cases} interval assignments; only the generating strip fails the ordinary split.")


if __name__ == '__main__':
    check_strip()
    check_comparison()
    check_guarded_split()
