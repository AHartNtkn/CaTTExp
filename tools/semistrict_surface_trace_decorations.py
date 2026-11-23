"""Verify trace occurrence transport and the two height calculations under composition."""

from collections import Counter
from fractions import Fraction
from itertools import product


def step(wires, offset, mark):
    source, target = mark
    inputs = wires[offset:offset + source]
    assert source > 0 and len(inputs) == source
    event = mark, inputs
    outputs = tuple((event, i) for i in range(target))
    return wires[:offset] + outputs + wires[offset + source:], event


def check_occurrences(counts):
    marks = list(product((1, 2), (1, 2, 3)))
    for chosen in product(marks, repeat=3):
        widths = [s for s, t in chosen]
        initial = tuple(range(sum(widths) + 2))
        positions = [0, widths[0] + 1, sum(widths[:2]) + 2]

        def execute(order):
            wires, done, events = initial, set(), {}
            for i in order:
                offset = positions[i] + sum(chosen[j][1] - widths[j] for j in done if j < i)
                wires, events[i] = step(wires, offset, chosen[i])
                done.add(i)
            return wires, events

        reference, events = execute((0, 1, 2))
        for order in ((0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)):
            assert execute(order) == (reference, events)
            # Rewriting across an output and a surviving gap uses their actual
            # port histories, including after the two neighboring rewrites.
            follow = step(reference, chosen[0][1] - 1, (2, 1))
            assert step(execute(order)[0], chosen[0][1] - 1, (2, 1)) == follow
            counts['occurrence-preserving reorderings with follow-up'] += 1


def polygon(data, start, n, out):
    block = data[start:start + n]
    assert len(block) == n
    m = sum(x for x, y in block)
    a = sum(y for x, y in block)
    return (data[:start] + ((m / out, (a + 1) / out),) * out + data[start + n:],
            sum(x for x, y in data[:start]))


def run(data, steps):
    height = 0
    for operation in steps:
        data, delta = polygon(data, *operation)
        height += delta
    return data, height


def check_transfers(counts):
    for a, u, b, v in product(range(1, 4), repeat=4):
        left = tuple((Fraction(i + 5, 2), Fraction(i + 1, 3)) for i in range(a))
        right = tuple((Fraction(i + 4, 3), Fraction(i + 2, 5)) for i in range(b))
        # One polygon in the first block, two consecutive ones in the second.
        first = [(0, a, u)]
        second = [(0, b, v), (0, v, 2)]
        shifts = lambda steps, offset: [(i + offset, n, m) for i, n, m in steps]
        expected_l, hl = run(left, first)
        expected_r, hr = run(right, second)
        expected = (expected_l + expected_r, hl + hr + 2 * sum(x for x, y in left))
        assert run(left + right, first + shifts(second, u)) == expected
        assert run(left + right, shifts(second, a) + first) == expected
        counts['independent composite decorations'] += 1

        # Use a composite 2-cell with three polygons and an independent
        # event block. Compare its generic mixed cell to subdivided crossings.
        other = tuple((Fraction(i + 7, 2), Fraction(i + 2, 7)) for i in range(a + b))
        composite = first + shifts(second, u)
        _, before = run(left + right + other, composite)
        _, after = run(other + left + right, shifts(composite, len(other)))
        assert after - before == len(composite) * sum(x for x, y in other)
        cost = sum(y for _ in composite for x, y in other)
        assert cost == len(composite) * sum(y for x, y in other)
        # Moving past the other block's two new polygon occurrences changes
        # the crossed numbers in both signed facet families.
        new_other, _ = run(other, [(0, a, u), (u, b, v)])
        crossed_after = (len(composite) * sum(y for x, y in new_other)
                         + 2 * sum(y for x, y in expected[0]))
        crossed_before = cost + 2 * sum(y for x, y in left + right)
        assert crossed_after - crossed_before == 2 * len(composite) * 2
        counts['two-sided composite tensor costs'] += 1


if __name__ == '__main__':
    counts = Counter()
    check_occurrences(counts)
    check_transfers(counts)
    for label, total in sorted(counts.items()):
        print(f'{total:,} {label}')
