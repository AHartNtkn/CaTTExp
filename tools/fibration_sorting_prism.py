#!/usr/bin/env python3
"""A family with unbounded erased-token counts in the net and finite exact middle cells."""
import argparse
from collections import Counter
from fibration_factor_search import Rule, Stage


def check(n):
    if n < 1:
        raise ValueError("multiplicity must be positive")
    arrows = {"a": ("X", "Y"), "b": ("Y", "X"), "f": ("X", "X"),
              "i": ("Y", "Y"), "j": ("Y", "Y")}
    start_h, end_h = "i" + "j" * n, "j" * n + "i"
    rules = {"s": Rule("X", "", "f"), "h": Rule("Y", "", start_h),
             "k": Rule("Y", "ij", "ji"), "u": Rule("X", "", "ba"),
             "a": Rule("X", end_h + "a", "af"),
             "i": Rule("Y", "fb", "bi"), "j": Rule("Y", "b", "bj")}
    stage = Stage(arrows, rules)
    before = (("j", 1),) * n + (("i", 0),)
    after = (("i", 0),) + (("j", 0),) * n
    prisms = {
        "A": ("X", "a", (("s", 1),),
              (("h", 0),) + tuple(("k", i) for i in range(n)) + (("a", 0),)),
        "H": ("Y", "b", (("h", 1),), (("s", 0),) + before),
        "K": ("Y", "fb", (("j", 1), ("i", 0), ("k", 1)), (("i", 0), ("j", 0))),
        "M": ("X", "f", (("u", 1),) + after + (("a", 1),), (("u", 0),)),
    }
    paths = list(stage.backwards("X", "", "baf", {"u"}, 1))
    cells, index = stage.quotient(paths)
    edges = stage.edges("X", "", cells, index, prisms)
    initial = index[(("u", 0), ("s", 2))]
    reached, stack = {initial}, [initial]
    while stack:
        x = stack.pop()
        for a, _, b in edges:
            if x == a and b not in reached:
                reached.add(b)
                stack.append(b)
    # Every contextual move in this example stays inside the enumerated set.
    # Verify exactly one successor at each reachable state and a closed orbit.
    orbit, x = [], initial
    for name in ("A", "H") + ("K",) * n + ("M",):
        options = [(g, b) for a, g, b in edges if a == x]
        assert len(options) == 1 and options[0][0] == name, options
        orbit.append(x)
        x = options[0][1]
    assert x == initial and len(set(orbit)) == len(orbit) == len(reached)
    # Check a symbolic pump and drain by firing the actual face multisets.
    def fire(marking, name):
        _, _, src, tgt = prisms[name]
        consume = Counter(g for g, _ in src)
        assert consume <= marking
        return marking - consume + Counter(g for g, _ in tgt)
    marking = Counter(u=1, s=1)
    for name in ("A", "H", "M"):
        marking = fire(marking, name)
    assert marking == Counter(u=1, s=1, k=n)
    for name in ("A", "H") + ("K",) * (2*n) + ("M",):
        marking = fire(marking, name)
    assert marking == Counter(u=1, s=1)
    print(f"n={n} writings={len(paths)} cells={len(cells)} edges={len(edges)} "
          f"reachable={len(reached)} exact_peak_k={max(sum(g=='k' for g,_ in cells[v][0]) for v in reached)} "
          f"net_gain_k={n}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="*", default=[1, 2, 3])
    for n in parser.parse_args().n:
        check(n)
