#!/usr/bin/env python3
"""Enumerate marked 3-moves on a guarded birth/change/death base pasting."""
import argparse
from collections import deque
from fibration_factor_search import Rule, Stage


def check(n, erase):
    # Traversal meets a (or b) before t in the displayed right-to-left word.
    obj = "x"
    base = {"u": ("", "a"), "w": ("ta", "tb"), "v": ("b", "")}
    rules = {name: Rule(obj, s, t) for name, (s, t) in base.items()}
    for c in "abt":
        rules[c] = Rule(obj, ("" if erase and c == "t" else "g") + c, c + "g")
    stage = Stage({c: (obj, obj) for c in "abtg"}, rules)
    prisms = {
        "U": (obj, "g", (("u", 1), ("a", 0)), (("u", 0),)),
        "W": (obj, ("" if erase else "g") + "ta",
              (("w", 0 if erase else 1), ("t", 0), ("b", 1)),
              (("t", 0), ("a", 1), ("w", 0))),
        "V": (obj, "gb", (("v", 1),), (("b", 0), ("v", 0))),
    }
    source = ("" if erase else "g"*n) + "t"
    target = "t" + "g"*n

    def projection(path):
        return tuple((name, len(word[:pos].replace("g", "")))
                     for word, (name, pos) in zip(stage.slices(obj, source, path), path)
                     if name in base)

    required = (("u", 1), ("w", 0), ("v", 1))
    def allowed(remaining, name, word, pos):
        return (name, len(word[:pos].replace("g", ""))) == required[remaining-1]

    paths = list(stage.backwards(obj, source, target, base, 3, allowed))
    assert all(projection(p) == required for p in paths)
    cells, index = stage.quotient(paths)
    edges = stage.edges(obj, source, cells, index, prisms)

    # Kahn's algorithm checks the actual quotient graph, including self-edges.
    successors = [[] for _ in cells]
    indegree = [0] * len(cells)
    for a, _, b in edges:
        successors[a].append(b)
        indegree[b] += 1
    queue = deque(i for i, d in enumerate(indegree) if not d)
    length = [0] * len(cells)
    processed = 0
    while queue:
        a = queue.popleft()
        processed += 1
        for b in successors[a]:
            length[b] = max(length[b], length[a] + 1)
            indegree[b] -= 1
            if not indegree[b]:
                queue.append(b)
    assert processed == len(cells) > 0
    print(f"erase={erase} n={n} writings={len(paths)} cells={len(cells)} "
          f"moves={len(edges)} longest={max(length)}")


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("n", type=int, nargs="*", default=[1,2,3])
    for n in p.parse_args().n:
        for erase in (False, True):
            check(n, erase)
