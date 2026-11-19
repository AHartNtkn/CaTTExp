"""Verify the weight primitive, unary tensor routes, and windows of a binary join."""

import sys
from collections import Counter
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from gray_globe_comparison import atom, boundary, face


def generators(tree, address=()):
    for vertex in range(len(tree) + 1):
        yield address + (vertex,)
    for branch, child in enumerate(tree):
        yield from generators(child, address + (branch,))


def tensor_boundary(basis):
    sign = 1
    for index, generator in enumerate(basis):
        degree = len(generator) - 1
        if degree:
            for side, coefficient in enumerate((-1, 1)):
                boundary_face = generator[:-2] + (generator[-2] + side,)
                yield basis[:index] + (boundary_face,) + basis[index + 1:], sign * coefficient
        sign *= (-1) ** degree


def primitive(basis):
    degrees = [len(g) - 1 for g in basis]
    assert sum(degrees) == 3
    value = 0
    for pivot, generator in enumerate(basis):
        upper = degrees.copy()
        upper[pivot] += 1
        if max(upper) <= 2 and not any(upper[:pivot]):
            value += 2 * generator[-1]
    return value


def check_primitive():
    # Nonuniform strings of suspensions give heights greater than one at both
    # degrees used in the primitive. Test all zero-factor placements as well.
    point = ()
    interval = (point, point, point)
    surface = (interval, point, interval)
    solid = (surface, interval)
    four = (solid, surface)
    count = 0
    patterns = set()
    for shape in [(four,), (four, solid), (surface, interval, solid),
                  (interval, surface, interval, interval)]:
        for basis in product(*(generators(branch) for branch in shape)):
            degrees = tuple(len(g) - 1 for g in basis)
            if sum(degrees) != 4:
                continue
            value = sum(sign * primitive(g) for g, sign in tensor_boundary(basis))
            assert value == (2 if max(degrees) <= 2 else 0)
            patterns.add(tuple(d for d in degrees if d))
            count += 1
    assert patterns == {(4,), (3, 1), (1, 3), (2, 2), (2, 1, 1),
                        (1, 2, 1), (1, 1, 2), (1, 1, 1, 1)}
    return count


def compose(left, right, cut):
    """Strict tableau composition, padding an operand by identities as needed."""
    assert left[:cut] == right[:cut] and left[cut][1] == right[cut][0]
    height = max(len(left), len(right))
    left += (((), ()),) * (height - len(left))
    right += (((), ()),) * (height - len(right))
    upper = tuple(tuple(tuple(sorted(x + y)) for x, y in zip(a, b))
                  for a, b in zip(left[cut + 1:], right[cut + 1:]))
    return left[:cut] + ((left[cut][0], right[cut][1]),) + upper


def cylinder_routes(dim, moving):
    # The moving input is the entire top globe. Lower levels here act with
    # this same input elevated inside the one-hole whiskering context.
    variable = (dim, 2)
    edge = (1, 2)

    def mixed(x, b):
        return atom((x, b) if moving == "left" else (b, x))

    if moving == "left":
        source = compose(mixed((0, 0), edge), mixed(variable, (0, 1)), 0)
        target = compose(mixed(variable, (0, 0)), mixed((0, 1), edge), 0)
    else:
        source = compose(mixed(variable, (0, 0)), mixed((0, 1), edge), 0)
        target = compose(mixed((0, 0), edge), mixed(variable, (0, 1)), 0)
    for cut in range(1, dim):
        before = mixed((cut, 0), edge)
        after = mixed((cut, 1), edge)
        if moving == "left":
            source, target = compose(before, target, cut), compose(source, after, cut)
        else:
            source, target = compose(source, after, cut), compose(before, target, cut)
    whole = mixed(variable, edge)
    assert (source, target) == (face(whole, 0), face(whole, 1))


def changed_window(before, after, lengths):
    prefix = 0
    while before[prefix] == after[prefix]:
        prefix += 1
    end = len(before)
    while before[end - 1] == after[end - 1]:
        end -= 1
    return (sum(lengths[x] for x in before[:prefix]),
            sum(lengths[x] for x in before[:end]))


def check_tableau_route(top, side, events):
    """Paste the contextual faces, including their fixed lower rows."""
    expected = face(top, side)
    current = Counter(expected[3][0])
    composite = None
    for generator in events:
        before = tuple(sorted(current.elements()))
        if generator is not None:
            change = boundary(generator)
            assert all(current[g] >= -n for g, n in change.items() if n < 0)
            current.update(change)
        after = tuple(sorted(current.elements()))
        active = () if generator is None else (generator,)
        step = expected[:3] + ((before, after), (active, active))
        composite = step if composite is None else compose(composite, step, 3)
    assert composite == expected


def check_join():
    routes = (("BCA", "CBA", "CAB", "ACB"), ("BCA", "ABC", "ACB"))
    count = 0
    for sizes in product(range(1, 6), repeat=3):
        lengths = dict(zip("ABC", sizes))
        for route in routes:
            windows = [changed_window(a, b, lengths) for a, b in zip(route, route[1:])]
            for cut in range(1, sum(sizes)):
                assert any(lo < cut < hi for lo, hi in windows)
                count += 1
        assert Counter(routes[0][0]) == Counter(routes[1][-1])
    return count


def check_mixed_disks():
    # a,b,c and h,f are the two routes of W. z varies an input;
    # its position determines which side of each layer is being used.
    left = (
        (("abcz", "hfz", "hzf", "zhf"), ("W0", None, "R1")),
        (("abcz", "abzc", "azbc", "zhf"), ("R0", None, "W1")),
    )
    right = (
        (("zabc", "azbc", "abzc", "abcz", "hfz"), ("T0", None, None, "W0")),
        (("zabc", "zhf", "hzf", "hfz"), ("W1", None, "T1")),
    )
    checks = 0
    for shape, routes in [((3, 2), left), ((2, 3), right)]:
        top = atom(tuple((degree, 2) for degree in shape))
        left_moves = shape[0] == 3
        labels = {}
        for side in range(2):
            labels[f"W{side}"] = (((2, side), (2, 2)) if left_moves else
                                   ((2, 2), (2, side)))
            if left_moves:
                labels[f"R{side}"] = ((3, 2), (1, side))
            else:
                labels[f"T{side}"] = ((1, side), (3, 2))
        (source, _), (target, _) = routes
        assert (source[0], source[-1]) == (target[0], target[-1])
        for side, (states, events) in enumerate(routes):
            assert len(events) + 1 == len(states)
            check_tableau_route(top, side, [labels.get(e) for e in events])
            for a, b, c, z in product(range(1, 4), repeat=4):
                for h in range(1, a + b + c):
                    masses = dict(a=a, b=b, c=c, z=z, h=h, f=a+b+c-h)
                    windows = []
                    for start, end in zip(states, states[1:]):
                        # A replacement can change the number of moves.
                        lo = 0
                        while lo < min(len(start), len(end)) and start[lo] == end[lo]:
                            lo += 1
                        tail = 0
                        while (tail < min(len(start), len(end)) - lo
                               and start[-1-tail] == end[-1-tail]):
                            tail += 1
                        assert sum(masses[x] for x in start) == sum(masses[x] for x in end)
                        windows.append((sum(masses[x] for x in start[:lo]),
                                        sum(masses[x] for x in start[:len(start)-tail])))
                    # The source route must cover its entire open window.
                    if side == 0:
                        for cut in range(1, a + b + c + z):
                            assert any(lo < cut < hi for lo, hi in windows)
                            checks += 1
    return checks


def check_right_variation():
    # A state retains the actual event order and the layer of B. Expand the
    # r_1 edge into h;e in both layers before comparing 4-paths.
    def paths(word, layer):
        if (word, layer) == ("BAC", 1):
            yield ""
        if not layer:
            for tail in paths(word, 1):
                yield "z" + tail
        moves = {"BCA": ("h", "ABC"), "ABC": ("e", "BAC")}
        if word in moves:
            event, target = moves[word]
            for tail in paths(target, layer):
                yield event + tail

    vertices = set(paths("BCA", 0))
    edges = set()
    for word in vertices:
        for source, target in [("hez", "zhe"), ("ez", "ze"), ("zh", "hz")]:
            if source in word:
                end = word.replace(source, target)
                assert end in vertices
                edges.add((word, end))
    assert len(vertices) == len(edges) == 3
    reached = {"zhe"}
    for _ in vertices:
        reached |= {end for start, end in edges if start in reached}
    assert "hez" not in reached


if __name__ == "__main__":
    print(f"Checked the primitive on {check_primitive()} degree-four basis tensors.")
    for dim, moving in product(range(1, 13), ("left", "right")):
        cylinder_routes(dim, moving)
    print("Both signed cylinder routes agree row by row through operand degree 12.")
    print(f"Checked {check_join()} interior cuts on the two binary-atom routes.")
    print(f"Checked both mixed disk signs and {check_mixed_disks()} source-window cuts.")
    check_right_variation()
    print("The right-variation fiber has three 4-paths and no reverse to its elementary exchange.")
