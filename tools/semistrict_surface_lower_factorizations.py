"""Test the relative free category's lower factorizations on finite graph arities."""
from functools import cache
from itertools import product


# Free categories of the point, a discrete pair, an interval, and an interval
# plus an isolated vertex. Functors here are exactly monotone vertex maps.
sizes = (1, 2, 2, 3)
low = (0, 1)
quotient = (0, 1, 0, 1)
component = ((0,), (0, 1), (0, 0), (0, 0, 1))
extra = ((2, 1), (1, 3), (3, 2))


@cache
def structural(p, q):
    return tuple(f for f in product(range(sizes[q]), repeat=sizes[p])
                 if p in low or f[0] == f[1] or (q not in low and f[:2] == (0, 1)))


def compose(f, g):
    return tuple(g[i] for i in f)


@cache
def cuts(p, q, f):
    return tuple((a, l, r) for a in low for l in structural(p, a)
                 for r in structural(a, q) if compose(l, r) == f)


def first_lower(objects, blocks):
    for i, ((p, q), f) in enumerate(zip(objects, blocks, strict=True)):
        # Compute the canonical cut using only the connected components.
        reps = tuple(component[p].index(j) for j in range(sizes[quotient[p]]))
        g = tuple(f[k] for k in reps)
        if compose(component[p], g) == f:
            return i, quotient[p], component[p], g
    return None


def check():
    words = factorizations = later = 0
    for n in range(3):
        for letters in product(extra, repeat=n):
            for p, q in product(range(4), repeat=2):
                objects = tuple(zip((p,) + tuple(b for _, b in letters),
                                    tuple(a for a, _ in letters) + (q,), strict=True))
                for blocks in product(*(structural(a, b) for a, b in objects)):
                    words += 1
                    first = first_lower(objects, blocks)
                    all_cuts = [(i, a, l, r) for i, ((s, t), f)
                                in enumerate(zip(objects, blocks, strict=True))
                                for a, l, r in cuts(s, t, f)]
                    assert bool(all_cuts) == (first is not None)
                    if first is None:
                        continue
                    j, canonical, collapse, tail = first
                    assert first in all_cuts
                    for i, a, l, r in all_cuts:
                        # Factor the first half of this actual cut at its own
                        # canonical prefix. Composing its remainder with the
                        # second half must recover the same suffix.
                        left_objects = objects[:i] + ((objects[i][0], a),)
                        left_blocks = blocks[:i] + (l,)
                        k, b, prefix, remainder = first_lower(left_objects, left_blocks)
                        assert (k, b, prefix) == (j, canonical, collapse)
                        if i == j:
                            assert compose(remainder, r) == tail
                        else:
                            later += 1
                            assert remainder == tail and compose(l, r) == blocks[i]
                        factorizations += 1
    assert later
    print(f'{words} words, {factorizations} lower factorizations, '
          f'{later} cuts after the canonical block.')


if __name__ == '__main__':
    check()
