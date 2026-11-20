"""Check the cut-one (3,3) disk and its delayed inner comparison in rounds 5/8."""

from itertools import product
from typing import NamedTuple

from interchange_double_variation import MOVES, SOURCE, TARGET, check_shell, check_units


class Arrow(NamedTuple):
    """An (m+1)-cell between additive m-tags (m = 7)."""

    source: int
    target: int
    label: int


def identity(tag):
    return Arrow(tag, tag, 0)


def then(left, right):
    assert left.target == right.source
    return Arrow(left.source, right.target, left.label + right.label)


def horizontal(left, right):
    return Arrow(left.source + right.source, left.target + right.target,
                 left.label + right.label)


class Filler(NamedTuple):
    """The unique (m+2)-cell with the given parallel boundaries."""

    source: Arrow
    target: Arrow


def filler(source, target):
    assert source[:2] == target[:2]
    return Filler(source, target)


def paste_fillers(first, second):
    assert first.target == second.source
    return filler(first.source, second.target)


def check_structure():
    tags = range(3)
    labels = range(2)
    arrows = [Arrow(a, b, u) for a, b, u in product(tags, tags, labels)]
    for a, b, c in product(tags, repeat=3):
        assert (a + b) + c == a + (b + c)
        assert a + 0 == 0 + a == a
        assert horizontal(identity(a), identity(b)) == identity(a + b)
    for x in arrows:
        assert then(identity(x.source), x) == then(x, identity(x.target)) == x
        assert horizontal(identity(0), x) == horizontal(x, identity(0)) == x
    for x, y, z in product(arrows, repeat=3):
        assert horizontal(horizontal(x, y), z) == horizontal(x, horizontal(y, z))
        if x.target == y.source and y.target == z.source:
            assert then(then(x, y), z) == then(x, then(y, z))

    pairs = [(x, y) for x, y in product(arrows, repeat=2) if x.target == y.source]
    for (x, y), (z, w) in product(pairs, repeat=2):
        assert then(horizontal(x, z), horizontal(y, w)) == horizontal(then(x, y), then(z, w))

    fillers = [filler(x, y) for x, y in product(arrows, repeat=2) if x[:2] == y[:2]]
    for f in fillers:
        assert paste_fillers(filler(f.source, f.source), f) == f
        assert paste_fillers(f, filler(f.target, f.target)) == f
        for g in fillers:
            if f.target == g.source:
                assert paste_fillers(f, g) == Filler(f.source, g.target)
            for compose in (horizontal, then):
                if compose == then and f.source.target != g.source.source:
                    continue
                # Both parallel routes around the square induce this same filler.
                top = compose(f.source, g.source)
                bottom = compose(f.target, g.target)
                for middle in (compose(f.target, g.source), compose(f.source, g.target)):
                    assert paste_fillers(filler(top, middle), filler(middle, bottom)) == filler(top, bottom)
    print(f"Tags 0..2 and labels 0..1: {len(arrows)} arrows, {len(pairs)**2} interchange squares, "
          f"{len(fillers)} parallel-boundary fillers.")


# These are the R10 moves between the five 5-paths (before suspension).
ROUTE_EDGES = {
    "exchange": ("P", "P'"), "Z_B": ("P'", "L"), "G": ("L", "D"),
    "Z_A": ("P", "R"), "H": ("R", "D"),
}


def route_tag(moves, marks):
    state = "P"
    total = 0
    for move in moves:
        source, state_after = ROUTE_EDGES[move]
        assert state == source
        total += marks[move]
        state = state_after
    assert state == "D"
    return total


def check_disk():
    check_shell()  # Includes the five raw paths, the two signed faces, and the top atom.
    check_units()
    # W=1 identifies its two routes, forcing h to be a unit when a,b,c,f
    # are units. Cartesian evaluation then records x and y independently.
    before, after = MOVES["W"]
    assert before == "abc" and after == "hf"
    for word in (SOURCE, TARGET):
        assert all(c in "abcfxhy" for c in word)
        assert (word.count("x"), word.count("y")) == (1, 1)
    for x_proper, y_proper in product((False, True), repeat=2):
        marks = dict.fromkeys(ROUTE_EDGES, 0)
        if x_proper and y_proper:
            marks.update(G=1, H=1)
        elif not x_proper:
            marks.update(G=0, H=marks["Z_B"])
        else:
            marks.update(G=marks["Z_A"], H=0)
        source = route_tag(("exchange", "Z_B", "G"), marks)
        target = route_tag(("Z_A", "H"), marks)
        assert source == target == int(x_proper and y_proper)
        principal = identity(source)
        assert (principal.source, principal.target, principal.label) == (source, target, 0)
    print("Shifted (3,3): P→P'→L→D and P→R→D both have tag 1 at proper G,H "
          "and tag 0 in all three unit cases.")


def probe(left, right, n):
    # Both Godement schedules have the same endpoint since the m-tags commute.
    return Arrow(right + left, left + right, int(right > 0 and left == n * right))


def check_probes():
    bound = 32
    for n in range(1, 2 * bound + 1):
        for tag in range(bound + 1):
            assert probe(0, tag, n) == probe(tag, 0, n) == identity(tag)
            power = 0
            for exponent in range(1, 2 * bound + 1):
                power += tag
                result = probe(power, tag, n)
                assert result[:2] == (power + tag, power + tag)
                assert (result != identity(power + tag)) == (tag > 0 and exponent == n)
        for left, right in product(range(bound + 1), repeat=2):
            result = probe(left, right, n)
            if n > bound:
                assert result == identity(left + right)
    print("Probe n=1..64 on powers 1..64 of tags 0..32: first detection at exponent n "
          "for every positive tag. All probes with n>32 vanish on [0,32]².")


def section_vertices(kept):
    """Old vertices representing the vertices after collapsing steps."""
    if not kept:
        return [0]
    retained = [i for i, active in enumerate(kept) if active]
    return [0, *retained[1:], len(kept)] if retained else [0]


def check_pruning():
    # A 2-dimensional pasting diagram is a string of suspended strings.
    # None marks a collapsed outer slot. A bit marks a retained inner edge.
    slots = [
        (size, mask)
        for size in range(3)
        for mask in (None, *product((False, True), repeat=size))
    ]
    checked = 0
    for width in range(4):
        for shape in product(slots, repeat=width):
            live = [mask is not None for _, mask in shape]
            outer = section_vertices(live)
            assert [sum(live[:v]) for v in outer] == list(range(sum(live) + 1))
            for new_slot, (lo, hi) in enumerate(zip(outer, outer[1:])):
                old_slot, = [i for i in range(lo, hi) if live[i]]
                mask = shape[old_slot][1]
                inner = section_vertices(mask)
                # Fixed padding on either side of the retained short interval.
                def lift(vertex):
                    return tuple((i, vertex if i == old_slot else 0) for i in range(lo, hi))

                def contract(word):
                    return tuple((sum(live[:i]), sum(shape[i][1][:v]))
                                 for i, v in word if live[i])

                for vertex, representative in enumerate(inner):
                    assert contract(lift(representative)) == ((new_slot, vertex),)
                for edge, (start, end) in enumerate(zip(inner, inner[1:])):
                    # Lift the 2-generator as a path of elementary updates
                    # of just the unpadded slot, and project every step.
                    projected = [contract(lift(v)) for v in range(start, end + 1)]
                    steps = [(a, b) for a, b in zip(projected, projected[1:]) if a != b]
                    assert steps == [(((new_slot, edge),), ((new_slot, edge + 1),))]
            checked += 1
    print(f"Pruning: {checked} marked suspended strings; both faces and all section composites agree.")


if __name__ == "__main__":
    check_disk()
    check_structure()
    check_probes()
    check_pruning()
