"""Check the native seed interval and the (4,4) bridge against its two raisings."""

from itertools import permutations

from interchange_cylinders import atom, compose, face
from interchange_double_variation import (
    BASE_EDGES, HISTORY, MOVES, PATHS, SOURCE, TARGET, between, path_table, rewrite,
)


def interval(bits):
    """4-paths from S to T, with each indicated 4-globe used once."""
    words = set()
    for route in ("abc", "hf"):
        for order in permutations(route + bits):
            if "".join(c for c in order if c not in bits) == route:
                words.add("".join(order))
    rules = {tag: move for tag, move in MOVES.items() if tag != "swap"}
    rules["ax"] = ("xa", "ax")
    rules["shifted join"] = ("ybx", "xyb")
    edges = {}
    for word in words:
        state = "S"
        edges[word] = []
        for i, letter in enumerate(word):
            # Atomic placements. The two branches ending at BAC cannot reach T.
            earlier = "xy" if HISTORY[state].index("A") < HISTORY[state].index("B") else "yx"
            rules["exchange"] = (earlier[::-1], earlier)
            for tag, (before, after) in rules.items():
                if word.startswith(before, i):
                    dest = word[:i] + after + word[i + len(before):]
                    assert dest in words
                    edges[word].append((tag, dest))
            if letter not in bits:
                start, end = BASE_EDGES[letter]
                assert start == state
                state = end
        assert state == "T"
    return edges


def check_seed(tag, bits, expected):
    edges = interval(bits)
    start, end = MOVES[tag]
    reached = {start}
    todo = [start]
    while todo:
        for label, dest in edges[todo.pop()]:
            if label == tag:
                continue
            if dest not in reached:
                reached.add(dest)
                todo.append(dest)
    assert reached == expected and end not in reached
    assert [(w, dest) for w in reached for label, dest in edges[w] if label == tag] == [(start, end)]
    print(f"{tag}: {len(edges)} vertices; bypass search reaches {sorted(reached)}")


def check_raw_faces():
    # A vertex records the rank-three word and which version of x and y
    # it contains. Thus different orders of independent updates remain visible.
    def walk(steps):
        word, i, j = SOURCE, 0, 0
        vertices = [(word, i, j)]
        for step in steps:
            if step == "X":
                assert i == 0 and "x" in word
                i = 1
            elif step == "Y":
                assert j == 0 and "y" in word
                j = 1
            else:
                word = rewrite(word, step)
            vertices.append((word, i, j))
        assert vertices[-1] == (TARGET, 1, 1)
        return vertices

    def raised_face(old, moving, p, rank, side):
        # At the first rank above the bottom, layer 0 appends the
        # terminal insertion; layer 1 prepends the initial insertion.
        reversed_bridge = moving == "Y" and (rank - p) % 2
        layer = side ^ int(reversed_bridge)
        return old + (moving,) if layer == 0 else (moving,) + old

    d = PATHS["D"]
    old_positive = raised_face(d, "Y", 3, 4, 1)
    start, end = (raised_face(old_positive, "X", 3, 4, i) for i in (0, 1))
    small_start, small_end = (raised_face(d, "X", 3, 4, i) for i in (0, 1))
    middle = small_start + ("Y",)
    assert start == d + ("Y", "X") and end == small_end + ("Y",)
    before, after, final = map(walk, (start, middle, end))
    assert before[:-2] == after[:-2] and before[-1] == after[-1]
    assert before[-3][0].index("x") < before[-3][0].index("y")
    assert after[-2:] == final[-2:]
    assert len({tuple(path) for path in (before, after, final)}) == 3


def check_bridge():
    # Identify the raw route D with the positive rank-four tensor hemisphere.
    assert path_table(PATHS["D"]) == face(face(atom(((3, 2), (3, 2))), 1), 1)

    def row(cell, rank, side):
        while len(cell) > rank + 1:
            cell = face(cell, side)
        return cell

    # Four copies of the disk, for the independent x and y layers.
    layers = {(i, j): atom(((3, i), (3, j))) for i in (0, 1) for j in (0, 1)}
    d = {ij: row(cell, 4, 1) for ij, cell in layers.items()}

    def change_x(j, side):
        return between(row(layers[0, j], 3, side), row(layers[1, j], 3, side),
                       ((4, 2), (0, 1 ^ side)))

    def change_y(i):
        return between(row(layers[i, 0], 3, 1), row(layers[i, 1], 3, 1),
                       ((0, 1), (4, 2)))

    right_raised = [compose(d[i, 0], change_y(i), 3) for i in (0, 1)]
    for i in (0, 1):
        assert right_raised[i] == row(atom(((3, i), (4, 2))), 4, 1)

    start = compose(right_raised[0], change_x(1, 1), 3)
    middle = compose(compose(d[0, 0], change_x(0, 1), 3), change_y(1), 3)
    end = compose(change_x(0, 0), right_raised[1], 3)
    # Gray forgets the positional exchange, but detects the smaller bridge.
    # Compute that bridge on y^0, then attach the final Y by whiskering.
    assert start == middle
    top = ((4, 2), (1, 0))
    small = between(compose(d[0, 0], change_x(0, 1), 3),
                    compose(change_x(0, 0), d[1, 0], 3), top)
    direct = between(start, end, top)
    assert direct == compose(small, change_y(1), 3)
    assert direct[-1][0] == (top,)
    assert {((4, 2), (0, 0)), ((0, 1), (4, 2))} <= set(start[-1][0])
    print("Both rank raisings, forward raw exchange, common Gray table and both pure inputs checked.")


if __name__ == "__main__":
    check_seed("W", "", {"abc"})
    check_seed("K", "x", {"axbc"})
    check_seed("J", "xy", {"yaxbc", "ayxbc", "yxhf"})
    check_raw_faces()
    check_bridge()
