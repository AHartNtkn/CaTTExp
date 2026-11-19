"""Evaluate the support-free degree-four equations and the loop on the 2 by 2 grid."""

from itertools import product
from math import inf


def compose(cut, left, right):
    assert len(left) == len(right)
    common = max(0, cut - 1)  # The first recorded coordinate has global degree two.
    assert left[:common] == right[:common]
    return left[:common] + tuple(a + b for a, b in zip(left[common:], right[common:]))


def lift(cell, degree):
    return cell + (0,) * (degree - len(cell) - 1)


def padded(cell, context, cut):
    return compose(cut, cell, lift(context, len(cell) + 1))


def e(z):
    return inf if z else 0


def crossing(u, v):
    return u + v, u * v


def left_naturality(a, v):
    u, m = a
    return u + v, u * v + m, e(m * v)


def right_naturality(u, b):
    v, n = b
    return u + v, u * v + n, e(u * n)


def inner(a, b):
    u, m = a
    v, n = b
    return u + v, m + n, m * n


def join(a, b):
    u, m = a
    v, n = b
    return u + v, u * v + m + n, e(m * v)


def check():
    weights = range(4)
    inputs = [(u, m) for u, m in product(weights, repeat=2) if u or not m]
    for a, b in product(inputs, repeat=2):
        u, m = a
        v, n = b
        square = inner(b, a)
        contextual_square = padded(square, crossing(u, v), 2)
        left = padded(left_naturality(a, v), (u + v, n), 2)
        right = padded(right_naturality(u, b), (u + v, m), 2)
        assert compose(3, join(a, b), contextual_square) == left
        assert compose(3, compose(3, right, contextual_square), left) == compose(3, join(a, b), right)
        if not m:
            assert join(a, b)[-1] == 0
        if not n:
            assert join(a, b) == left_naturality(a, v)

        for z in weights:
            # Whiskering the varying input adds one contextual inner crossing.
            assert left_naturality(padded(a, (z,), 1), v)[-1] + inner(crossing(z, v), a)[-1] == left[-1]
            assert right_naturality(u, padded(b, (z,), 1))[-1] + inner(b, crossing(u, z))[-1] == right[-1]
            assert left_naturality(crossing(u, v), z) == right_naturality(u, crossing(v, z))
            assert crossing(u + v, z)[-1] == crossing(u, z)[-1] + crossing(v, z)[-1]
            assert right_naturality(u + z, b)[-1] == right[-1] + right_naturality(z, b)[-1]
            assert left_naturality(a, v + z)[-1] == left[-1] + left_naturality(a, z)[-1]
            if u or not z:
                other = (u, z)
                combined = compose(2, a, other)
                assert left_naturality(combined, v)[-1] == left[-1] + left_naturality(other, v)[-1]
                assert inner(combined, b)[-1] == inner(a, b)[-1] + inner(other, b)[-1]
            if v or not z:
                other = (v, z)
                combined = compose(2, b, other)
                assert right_naturality(u, combined)[-1] == right[-1] + right_naturality(u, other)[-1]
                assert inner(a, combined)[-1] == inner(a, b)[-1] + inner(a, other)[-1]

    single = crossing(1, 1)
    prefix = padded(single, (2,), 1)
    h = padded(padded(inner(single, single), prefix, 2), prefix, 2)
    w = crossing(2, 2)
    assert h[:-1] == w
    power = lift(w, 4)
    for k in range(101):
        assert power == (*w, k)
        power = compose(3, power, h)
    print(f"Checked the weight identities on {len(inputs) ** 2} pairs of typed inputs.")
    print("H has boundary (4, 4) on both sides. Powers 0 through 100 have top weights 0 through 100.")


if __name__ == "__main__":
    check()
