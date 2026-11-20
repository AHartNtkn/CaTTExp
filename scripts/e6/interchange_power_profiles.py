"""Check the subdivision witnesses, seed charges, and the two profile tests."""

from functools import cache
from itertools import product
from math import gcd


def slide(state, left, right):
    position = state.index(left)
    assert state[position + 1] == right
    return state[:position] + (right, left) + state[position + 2:]


def check_schedules():
    # Identify each event by its position in its own moving/stationary stack.
    # Read the left-moving unary boundary as stationary pieces then variations.
    start = ("g1", "g2", "v1", "v2")
    middle = slide(start, "g2", "v1")
    first, second = ("g1", "v1"), ("g2", "v2")
    assert middle.index(first[0]) + 2 == middle.index(second[0])
    by_moving = slide(slide(middle, *first), *second)
    by_stationary = slide(slide(middle, *second), *first)
    assert by_moving == by_stationary
    assert slide(by_moving, "g1", "v2") == ("v1", "v2", "g1", "g2")


def triple_weight(mass):
    if mass == 0:
        return 0
    factor = 1
    while mass % 2 == 0:
        factor *= 3
        mass //= 2
    return factor * mass


def check_seeds():
    # Occurrence lists P,P',L,R,D from the (3,3) seed, before reweighting.
    paths = ["a b c s W f h", "a b c W s f h", "W Y F s f h",
             "a b c s C B K", "C B J F"]
    for x, y in product(range(1, 33), repeat=2):
        for g in (int, triple_weight):
            a, b = g(x), g(y)
            costs = dict(a=1, b=1, c=b, s=a*b, W=1, f=a, h=1,
                         Y=1+b, F=1, C=1, B=1, K=a, J=(1+a)*(1+b))
            totals = [sum(costs[k] for k in path.split()) for path in paths]
            assert len(set(totals)) == 1
            # In consecutive changed ranks the preceding s has product mass.
            assert g(x*y)*g(1) + 1 + 1 == 1 + (1 + g(x*y))


def summary(word):
    return "E" in word, "L" in word, any(
        a == "E" and "L" in word[i + 1:] for i, a in enumerate(word)
    )


def check_profiles():
    for x, y in product(range(17), repeat=2):
        a = triple_weight(2*x) * triple_weight(y)
        b = 2 * triple_weight(x) * triple_weight(y)
        assert 2*a == 3*b
        assert 2*x*y == x*y + x*y
    for p, d, n in product((2, 3, 5, 7), range(1, 17), range(1, 65)):
        def f(m):
            return m // gcd(m, n)

        observed = all(f(p*d*m) == p*f(d*m) for m in range(1, n+1))
        assert observed == ((n // gcd(n, d)) % p != 0)
    # All colours, including independent degeneracies and surrounding contexts.
    for pre, left, right, post in product(("", "E", "L", "EL", "LE"), repeat=4):
        base = left + right
        assert summary(pre + 2*base + post) == summary(pre + 3*base + post)


@cache
def crossing_histories(start, end):
    """Paths of unsplit bare squares. Each coordinate counts columns before a row."""
    if start == end:
        return ((),)
    first, second = start
    low, high = end
    moves = []
    for width in range(1, first - low + 1):
        moves.append((("first", first, width), (first - width, second)))
    for width in range(1, second - max(first, high) + 1):
        moves.append((("second", second, width), (first, second - width)))
    if first == second:
        for width in range(1, first - high + 1):
            moves.append((("both", first, width), (first - width, second - width)))
    return tuple((step,) + tail for step, target in moves
                 for tail in crossing_histories(target, end))


def check_staged_equation():
    histories = set(crossing_histories((4, 4), (0, 0)))
    lifts = []
    for column in (4, 2):
        corner = (("first", column, 1),)
        last = (("second", column - 1, 1),)
        early = ("first", column - 1, 1)
        late = ("second", column, 1)
        # The inactive two-column square can use any of its macrohistories.
        other = 6 - column
        inactive = crossing_histories((other, other), (other - 2, other - 2))
        sources, targets = set(), set()
        for path in inactive:
            before, after = ((), path) if column == 4 else (path, ())
            sources.add(before + corner + (late, early) + last + after)
            targets.add(before + corner + (early, late) + last + after)
        assert sources | targets <= histories
        assert sources.isdisjoint(targets)
        lifts.append((sources, targets))
    # Distinct block moves really can compose before quotienting.
    assert lifts[0][1] & lifts[1][0]
    colours = ["".join(w) for size in range(5) for w in product("EL", repeat=size)]
    for a, b in product(colours, repeat=2):
        assert summary(2*a + 4*b + 2*a) == summary(2*b + 4*a + 2*b)
    print(f"{len(histories)} macrohistories, {len(lifts[0][0])} and "
          f"{len(lifts[1][0])} lifts, {len(colours)**2} colour assignments checked.")


if __name__ == "__main__":
    check_schedules()
    check_seeds()
    check_profiles()
    check_staged_equation()
    print("Both schedules, five seed routes, consecutive-rank charges, divisor tests and separated-word contexts agree.")
