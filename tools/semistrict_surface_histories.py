"""Check the directed exchange peaks for histories with nonunique factorizations."""

from collections import Counter
from functools import cache
from itertools import product


# Work over the one-object category of the two-element group. Both choices of
# the first factor give the same composite with a suitable second factor.
def atom(i, j):
    return ("atom", i, j)


def left(event, idle):
    return ("left", event, idle)


def right(idle, event):
    return ("right", idle, event)


@cache
def ends(event):
    tag, x, y = event
    if tag == "atom":
        return x, y
    if tag == "left":
        return tuple(k ^ y for k in ends(x))
    return tuple(x ^ k for k in ends(y))


@cache
def exchange(first, second):
    a, x, y = first
    b, u, v = second
    if a == b == "left" and y == v:
        inner = exchange(x, u)
        if inner:
            return tuple(left(e, y) for e in inner)
    if a == b == "right" and x == u:
        inner = exchange(y, v)
        if inner:
            return tuple(right(x, e) for e in inner)
    if a == "right" and b == "left" and x == ends(u)[0] and v == ends(y)[1]:
        return left(u, ends(y)[0]), right(ends(u)[1], y)
    return None


def walk(word, steps):
    for pos in steps:
        change = exchange(*word[pos:pos + 2])
        assert change is not None
        word = word[:pos] + change + word[pos + 2:]
    return word


def check():
    counts = Counter()
    events = set(atom(s, t) for s, t in product(range(2), repeat=2))
    for _ in range(3):
        events |= {w for e, k in product(events, range(2)) for w in (left(e, k), right(k, e))}
    previous = {e: [] for e in events}
    following = {e: [] for e in events}
    for first, second in product(events, repeat=2):
        if ends(first)[1] != ends(second)[0]:
            continue
        counts["composable event pairs"] += 1
        change = exchange(first, second)
        if change:
            x, y = change
            assert ends(x)[0] == ends(first)[0] and ends(y)[1] == ends(second)[1]
            assert ends(x)[1] == ends(y)[0]
            previous[second].append(first)
            following[first].append(second)
            counts["directed swaps"] += 1
    for middle in events:
        for first, last in product(previous[middle], following[middle]):
            word = first, middle, last
            assert walk(word, (0, 1, 0)) == walk(word, (1, 0, 1))
            counts["overlapping exchange peaks"] += 1
    for kind, count in sorted(counts.items()):
        print(f"{count:,} {kind}")


if __name__ == "__main__":
    check()
