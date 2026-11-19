"""Paste the signed (3,3) shell and check its raw paths and both unit faces."""

from collections import Counter
from itertools import product

from interchange_cylinders import atom, boundary, compose, face


MOVES = {
    "ay": ("ya", "ay"), "by": ("yb", "by"), "cy": ("yc", "cy"),
    "hy": ("yh", "hy"), "fy": ("yf", "fy"), "swap": ("yx", "xy"),
    "cx": ("cx", "xc"), "bx": ("bx", "xb"), "fx": ("fx", "xf"),
    "hx": ("hx", "xh"), "W": ("abc", "hf"), "K": ("axbc", "xhf"),
    "J": ("yaxbc", "xhyf"),
}
PATHS = {
    "P": ("ay", "by", "cy", "swap", "W", "fx", "hx"),
    "swapped": ("ay", "by", "cy", "W", "swap", "fx", "hx"),
    "L": ("W", "hy", "fy", "swap", "fx", "hx"),
    "R": ("ay", "by", "cy", "swap", "cx", "bx", "K"),
    "D": ("cx", "bx", "J", "fy"),
}
SOURCE = "yabcx"
TARGET = "xhfy"
TOP = atom(((3, 2), (3, 2)))
HISTORY = dict(S="BCA", V0="CBA", V1="CAB", T="ACB", U0="ABC")
BASE_EDGES = dict(a=("S", "V0"), b=("V0", "V1"), c=("V1", "T"),
                  h=("S", "U0"), f=("U0", "T"))


def rewrite(word, name):
    before, after = MOVES[name]
    assert word.count(before) == 1
    return word.replace(before, after)


def word_chain(word):
    state = "S"
    x = y = 0
    chain = []
    for letter in word:
        history = HISTORY[state]
        if letter == "x":
            assert x == 0
            x = 1
            chain.append(((3, 2), (0, int(history.index("A") < history.index("C")))))
        elif letter == "y":
            assert y == 0
            y = 1
            chain.append(((0, int(history.index("B") > history.index("C"))), (3, 2)))
        else:
            start, end = BASE_EDGES[letter]
            assert state == start
            state = end
            if letter in "af":
                chain.append(((1, int(letter == "f")), (2, y)))
            elif letter in "ch":
                chain.append(((2, x), (1, int(letter == "h"))))
    assert (state, x, y) == ("T", 1, 1)
    return tuple(sorted(chain))


def step_table(prefix, before, after, basis):
    expected = Counter(after)
    expected.subtract(before)
    differential = Counter() if basis is None else boundary(basis)
    assert differential == expected
    high = () if basis is None else (basis,)
    return prefix + ((before, after), (high, high))


def path_table(names):
    word = SOURCE
    result = None
    for name in names:
        before, _ = MOVES[name]
        prefix = word[:word.index(before)]
        basis = None
        if name == "W":
            basis = ((2, int("x" in prefix)), (2, int("y" in prefix)))
        elif name in ("K", "J"):
            basis = ((2, 1), (2, int(name == "J" or "y" in prefix)))
        elif name in ("ay", "fy"):
            basis = ((1, int(name == "fy")), (3, 2))
        elif name in ("cx", "hx"):
            basis = ((3, 2), (1, int(name == "hx")))
        elif name == "swap":
            # At T, A precedes B, so putting x first is the forward exchange.
            assert all(letter in prefix for letter in "abc") or all(letter in prefix for letter in "hf")
        after = rewrite(word, name)
        step = step_table(TOP[:3], word_chain(word), word_chain(after), basis)
        result = step if result is None else compose(result, step, 3)
        word = after
    assert word == TARGET
    return result


def check_shell():
    tables = {name: path_table(moves) for name, moves in PATHS.items()}
    assert tables["P"] == face(face(TOP, 0), 0)
    assert tables["D"] == face(face(TOP, 1), 1)
    routes = [(("P", "swapped", "L", "D"), (None, ((2, 0), (3, 2)), ((3, 2), (2, 1)))),
              (("P", "R", "D"), (((3, 2), (2, 0)), ((2, 1), (3, 2))))]
    for side, (path, bases) in enumerate(routes):
        result = None
        for start, end, basis in zip(path, path[1:], bases):
            left, right = tables[start], tables[end]
            assert left[:-1] == right[:-1]
            step = step_table(left[:-1], left[-1][0], right[-1][0], basis)
            result = step if result is None else compose(result, step, 4)
        assert result == face(TOP, side)


def specialize(names, unit):
    def erase(word):
        return word.replace(unit, "")
    word = SOURCE
    trace = [erase(word)]
    for name in names:
        after = rewrite(word, name)
        if name == "J" and unit == "x":
            trace.append(rewrite(erase(word), "W"))
            assert rewrite(trace[-1], "hy") == erase(after)
        if trace[-1] != erase(after):
            trace.append(erase(after))
        word = after
    return trace


def check_units():
    left = [["abcz", "hfz", "hzf", "zhf"], ["abcz", "abzc", "azbc", "zhf"]]
    right = [["zabc", "azbc", "abzc", "abcz", "hfz"], ["zabc", "zhf", "hzf", "hfz"]]
    for name, moves in PATHS.items():
        assert [s.replace("x", "z") for s in specialize(moves, "y")] == left[name in ("R", "D")]
        assert [s.replace("y", "z") for s in specialize(moves, "x")] == right[name in ("L", "D")]


def check_windows():
    checks = 0
    for a, b, c, x, y in product(range(1, 4), repeat=5):
        for h in range(1, a+b+c):
            weights = dict(a=a, b=b, c=c, x=x, y=y, h=h, f=a+b+c-h)
            total = sum(weights[k] for k in SOURCE)
            for name in ("L", "R"):
                word = SOURCE
                possible = set(range(1, total))
                for move in PATHS[name]:
                    before, _ = MOVES[move]
                    at = word.index(before)
                    lo = sum(weights[k] for k in word[:at])
                    hi = lo + sum(weights[k] for k in before)
                    possible.difference_update(range(lo+1, hi))
                    word = rewrite(word, move)
                    assert sum(weights[k] for k in word) == total
                assert not possible
                checks += total-1
    return checks


def between(left, right, basis):
    assert left[:-1] == right[:-1]
    return step_table(left[:-1], left[-1][0], right[-1][0], basis)


def check_strip(p, moving):
    """Build the two slides on the old routes and whisker both old disk atoms."""
    def pair(variable, fixed):
        return (variable, fixed) if moving == "left" else (fixed, variable)

    disks = [atom(pair((p, side), (2, 2))) for side in range(2)]
    old = [[face(disk, side) for side in range(2)] for disk in disks]
    v = (p+1, 2)
    j = (p+1) % 2
    pure = []
    for side in range(2):
        vertex = (side ^ j ^ 1) if moving == "left" else side
        pure.append(between(face(old[0][0], side), face(old[1][0], side), pair(v, (0, vertex))))
    after = [compose(old[0][side], pure[1], p) for side in range(2)]
    before = [compose(pure[0], old[1][side], p) for side in range(2)]
    old_after = compose(disks[0], pure[1], p)
    old_before = compose(pure[0], disks[1], p)
    if moving == "left":
        slides = [between(after[side], before[side], pair(v, (1, side ^ (p % 2))))
                  for side in range(2)]
        routes = compose(old_after, slides[1], p+1), compose(slides[0], old_before, p+1)
    else:
        slides = [between(before[side], after[side], pair(v, (1, side))) for side in range(2)]
        routes = compose(slides[0], old_after, p+1), compose(old_before, slides[1], p+1)
    top = atom(pair(v, (2, 2)))
    assert routes == (face(top, 0), face(top, 1))


def check_prism(p, q, moving):
    """Lift successive globular rows; p is the old moving degree, q the fixed degree."""
    def pair(variable, fixed):
        return (variable, fixed) if moving == "left" else (fixed, variable)

    def hemisphere(disk, rank, side):
        while len(disk) > rank+1:
            disk = face(disk, side)
        return disk

    disks = [atom(pair((p, side), (q, 2))) for side in range(2)]
    varying = (p+1, 2)
    contexts = [lambda disk: disk, lambda disk: disk]
    new = atom(pair(varying, (q, 2)))
    for rank in range(p, p+q+1):
        delta = rank-p
        sign = 1 if moving == "left" else (-1)**delta
        bridges = []
        for side in range(2):
            ends = [contexts[layer](hemisphere(disk, rank, side)) for layer, disk in enumerate(disks)]
            if sign == -1:
                ends.reverse()
            fixed_side = side ^ (p % 2) if moving == "left" else side
            fixed = (delta, 2 if delta == q else fixed_side)
            bridge = between(*ends, pair(varying, fixed))
            assert ends[side] == hemisphere(new, rank, side)
            bridges.append(bridge)
        if rank == p+q:
            assert bridges[0] == bridges[1] == new
            break
        first = 0 if sign == 1 else 1
        second = 1-first
        left_context, right_context = contexts[first], contexts[second]
        contexts[first] = lambda z, old=left_context, b=bridges[1], r=rank: compose(old(z), b, r)
        contexts[second] = lambda z, old=right_context, b=bridges[0], r=rank: compose(b, old(z), r)


if __name__ == "__main__":
    check_shell()
    check_units()
    cuts = check_windows()
    print("Both (3,3) routes have the exact signed tableaux; all five paths specialize at both units.")
    print(f"Checked {cuts} interior cuts in the two new 6-cell sources.")
    for degree, moving in product(range(3, 15), ("left", "right")):
        check_strip(degree, moving)
    print("Pasted both faces of the two infinite strips for new operand degrees 4 through 15.")
    for p, q, moving in product(range(3, 9), range(2, 9), ("left", "right")):
        check_prism(p, q, moving)
    print("All signed hemispheres and both top routes agree for 84 disk extensions.")
