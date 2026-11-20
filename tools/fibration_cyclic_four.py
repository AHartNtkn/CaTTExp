#!/usr/bin/env python3
"""Four-factors on deterministic 3-histories, including the collapsed D2 tensor D2."""
from collections import deque
from fibration_factor_search import Rule, Stage
from gray_globe_comparison import atom


def threshold_path(start, target, transitions):
    """Return a shortest path in the proven finite search interval, or None."""
    threshold = max((n for n, _ in transitions), default=0)
    jump = max((abs(d) for _, d in transitions), default=0)
    ceiling = max(start, target, threshold + 2 * jump)
    parent = {start: None}
    todo = deque([start])
    while todo:
        n = todo.popleft()
        if n == target:
            path = []
            while n is not None:
                path.append(n)
                n = parent[n]
            return path[::-1]
        for minimum, delta in transitions:
            after = n + delta
            if n >= minimum and 0 <= after <= ceiling and after not in parent:
                parent[after] = n
                todo.append(after)
    return None


def check():
    stage = Stage({c: ("x", "x") for c in "gt"},
                  {n: Rule("x", s, t) for n, s, t in
                   [("u", "", "t"), ("h", "", "g"), ("c", "gt", "tg")]})
    # Both creations occur once since the target word has one of each letter.
    def middle():
        for a in ("u", "h"):
            b = "h" if a == "u" else "u"
            for pos in (0, 1):
                path = ((a, 0), (b, pos))
                if tuple(stage.slices("x", "", path))[-1] == "tg":
                    yield path
                else:
                    yield path + (("c", 0),)

    cells, index = stage.quotient(middle())
    a = index[(("u", 0), ("h", 1))]
    b = index[(("u", 0), ("h", 0), ("c", 0))]
    prisms = {"D": ("x", "t", (("h", 1),), (("h", 0), ("c", 0))),
              "M": ("x", "g", (("u", 1), ("c", 0)), (("u", 0),))}
    moves = stage.edges("x", "", cells, index, prisms)
    assert moves == {(a, "D", b), (b, "M", a)}

    # Verify one-marker contexts (distinct contexts with the same endpoints matter).
    # At D the only other 2-step is u, needed to supply its input t. At M it is h.
    for name, (_, src_word, before, _) in prisms.items():
        other = "u" if name == "D" else "h"
        mark = Rule("x", src_word, tuple(stage.slices("x", src_word, before))[-1])
        marked = Stage(stage.arrows, {**stage.rules, "*": mark})
        contexts = []
        for pos in range(2):
            for p in [(("*", 0), (other, pos)), ((other, 0), ("*", pos))]:
                try:
                    result = tuple(marked.slices("x", "", p))[-1]
                except ValueError:
                    continue
                if result == "tg":
                    contexts.append(p)
        assert contexts == [((other, 0), ("*", 0))]

    # Map the globe atom along the two boundary maps collapsing the source edges.
    # In a pure degree, tensoring with an identity edge has zero top count.
    square = atom(((2, 2), (2, 2)))
    def surviving(row):
        return [(f[0], q[0]) for f, q in row if (1, 0) not in (f, q)]
    assert [surviving(row) for row in square[2]] == [[(0, 2), (2, 0)]] * 2
    negative, positive = (surviving(row) for row in square[3])
    assert negative == [] and sorted(positive) == [(1, 2), (2, 1)]
    # Both 2-poles have no c: the 4-rule at A inserts the unique D,M circuit.
    # The 2-poles already use the only h and u. Thus no extra 2-step context
    # can surround the rule; common prefix and suffix 3-histories are arbitrary.
    for source in range(16):
        for target in range(16):
            if source % 2 != target % 2:
                continue  # the endpoint 2-cells must agree
            for initial in (a, b):
                first_visit = int(initial != a)
                path = threshold_path(source, target, [(first_visit, 2)])
                assert (path is not None) == (source == target or
                                               (source >= first_visit and target > source))

    # A signed threshold system checks the search above both endpoint values.
    assert threshold_path(3, 4, [(3, 5), (8, -4)]) == [3, 8, 4]
    assert threshold_path(3, 5, [(3, 6), (9, -3)]) is None
    print("2 middle cells, 2 elementary 3-contexts, 1 elementary 4-context")
    print("4-rule inserts D,M at A; checked 256 parallel endpoint queries")


if __name__ == "__main__":
    check()
