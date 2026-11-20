"""Compare contextual Gray prism moves with simultaneous lifts along two edges."""
from functools import lru_cache

from fibration_factor_search import Rule, Stage


stage = Stage(
    {"I": ("X", "X"), "J": ("X", "X"), "i": ("Y", "Y"), "j": ("Y", "Y"),
     "a": ("X", "Y"), "b": ("Y", "Z")},
    {"r": Rule("X", "I", "I"), "s": Rule("X", "J", "J"),
     "h": Rule("Y", "i", "i"), "k": Rule("Y", "i", "i"),
     "A": Rule("X", "ia", "aI"), "B": Rule("X", "ja", "aJ"),
     "C": Rule("Y", "b", "bi"), "D": Rule("Y", "b", "bj")})

prisms = {
    "r": ("X", "ia", (("A", 0), ("r", 1)), (("h", 0), ("A", 0))),
    "s": ("X", "ja", (("B", 0), ("s", 1)), (("B", 0),)),
    "h": ("Y", "b", (("C", 0), ("h", 1)), (("C", 0),)),
    "k": ("Y", "b", (("C", 0), ("k", 1)), (("C", 0),)),
}


def regional_data(path):
    names = [name for name, _ in path]
    return names.count("r"), names.count("s"), "".join(n for n in names if n in "hk")


def region_moves(state):
    r, s, y = state
    if r:
        yield "r", (r - 1, s, y + "h")
    if s:
        yield "s", (r, s - 1, y)
    if y:
        yield y[0], (r, s, y[1:])


@lru_cache(None)
def reaches(state):
    result = {state}
    for _, target in region_moves(state):
        result.update(reaches(target))
    return result


def common(first, second):
    # The sum of the two prescribed counts bounds each region independently.
    x_bound = sum(first[:2]) + sum(second[:2])
    y_bound = len(first[2]) + len(second[2])
    words = [""]
    frontier = [""]
    for _ in range(y_bound):
        frontier = [c + w for w in frontier for c in "hk"]
        words.extend(frontier)
    return {(r, s, y) for r in range(x_bound + 1) for s in range(x_bound - r + 1)
            for y in words if {first, second} <= reaches((r, s, y))}


def raw_graph(bound):
    paths = [p for cost in range(bound + 1)
             for p in stage.backwards("X", "ba", "baIJ", set("rshk"), cost)]
    cells, index = stage.quotient(paths)
    keys = [regional_data(group[0]) for group in cells]
    assert len(set(keys)) == len(cells)
    assert all(regional_data(p) == keys[i] for i, group in enumerate(cells) for p in group)
    actual = {(keys[a], label, keys[b])
              for a, label, b in stage.edges("X", "ba", cells, index, prisms)}
    predicted = {(k, label, dst) for k in keys for label, dst in region_moves(k)}
    assert actual == predicted
    return paths, keys, actual


def check():
    paths, keys, actual = raw_graph(2)
    _, larger, edges = raw_graph(4)
    incoming = {k: set() for k in larger}
    for src, _, dst in edges:
        incoming[dst].add(src)

    def ancestors(target):
        found, todo = {target}, [target]
        while todo:
            new = incoming[todo.pop()] - found
            found.update(new)
            todo.extend(new)
        return found

    backwards = {k: ancestors(k) for k in keys}
    for first in keys:
        for second in keys:
            assert bool(common(first, second)) == bool(backwards[first] & backwards[second])
    assert common((1, 0, ""), (0, 1, "")) == {(1, 1, "")}
    assert not common((0, 0, "hk"), (0, 0, "kh"))
    for state in keys:
        assert (0, 0, "") in reaches(state)
    print(f"{len(paths)} writings, {len(keys)} cells, {len(actual)} contextual moves")
    print(f"{len(keys) ** 2} anchored pairs checked against contextual reachability")
    print("Independent residuals admit a common source; opposite ordered tails do not")


if __name__ == "__main__":
    check()
