"""Recover contextual four-generator counts from the two three-dimensional faces."""
from collections import Counter
from itertools import product

from gray_globe_comparison import atom, close_atoms, face


def subdivided_globe():
    # Two composable 2-generators on three parallel 1-arrows.
    return [(d, i) for d, n in enumerate((2, 3, 2)) for i in range(n)]


def differential(pair):
    result = Counter()
    sign = 1
    for axis, (d, i) in enumerate(pair):
        if d:
            start = i if d == 2 else 0
            for offset, coeff in ((0, -1), (1, 1)):
                corner = list(pair)
                corner[axis] = (d - 1, start + offset)
                result[tuple(corner)] += sign * coeff
        sign *= (-1) ** d
    return result


def full_strict_composition():
    """Independently close the actual Gray atoms under every composition."""
    labels = list(product(subdivided_globe(), repeat=2))
    cells = close_atoms([atom(pair, differential) for pair in labels], 4)
    tested = Counter()
    for cell in cells:
        wanted = Counter(cell[-1][0])
        if not wanted:
            continue
        before, after = (Counter(face(cell, side)[-1][0]) for side in (0, 1))
        recovered = Counter()
        for rho in range(2):
            flow = 0
            for wire in range(3):
                prism = ((2, rho), (1, wire))
                flow += before[prism] - after[prism]
                if wire < 2 and flow:
                    recovered[((2, rho), (2, wire))] = flow
            assert flow == 0
        assert recovered == wanted
        tested[sum(wanted.values())] += 1
    assert set(tested) == {1, 2, 3, 4}
    print("Nonidentity strict 4-cells by length:", sorted(tested.items()))


def erasing_window(counts):
    """Periodic t -> ta -> tb -> t base writing, with t(h)=h;k, t(k)=id."""
    wires = Counter()
    # Each tuple gives the input and output paths of one actual vertex.
    def add_side(path, counts_at_vertex, sign):
        carried = counts_at_vertex
        for wire in path:
            for color, count in enumerate(carried):
                wires[wire, color] += sign * count
            if wire[0] == "t":
                carried = (carried[0], carried[0])

    for i, (birth, change, death) in enumerate(counts):
        a, b = ("a", i), ("b", i)
        for incoming, outgoing, times in (
            ([], [a], birth),
            ([("t", i), a], [("t", i + 1), b], change),
            ([b], [], death),
        ):
            add_side(incoming, times, -1)
            add_side(outgoing, times, 1)

    change = [0, 0]
    for i, expected in enumerate(counts):
        change = [change[j] - wires[("t", i), j] for j in range(2)]
        birth = tuple(wires[("a", i), j] + change[0] for j in range(2))
        death = tuple(change[0] - wires[("b", i), j] for j in range(2))
        assert (birth, tuple(change), death) == expected
    assert all(change[j] == wires[("t", len(counts)), j] for j in range(2))


if __name__ == "__main__":
    full_strict_composition()
    for n in range(1, 9):
        # Unit columns check the entire linear map, including the erased colour.
        for col in range(6 * n):
            counts = [tuple(tuple(int(6*i + 2*k + j == col) for j in range(2))
                            for k in range(3)) for i in range(n)]
            erasing_window(counts)
    print("Recovered every column on 1 through 8 nullary windows with erasure.")
