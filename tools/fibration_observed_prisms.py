"""Check the three finite ranks in a split cup, including erased fibre events."""
from collections import Counter

from fibration_factor_search import Rule, Stage


stage = Stage(
    {"a": ("X", "Y"), "b": ("Y", "X"), "f": ("X", "X"), "g": ("Y", "Y")},
    {"u": Rule("X", "", "ba"), "s": Rule("X", "f", "f"),
     "h": Rule("Y", "g", "g"), "k": Rule("Y", "g", "g"),
     "A": Rule("X", "ga", "af"), "B": Rule("Y", "fb", "bg")})
prisms = {
    "As": ("X", "ga", (("A", 0), ("s", 1)), (("h", 0), ("k", 0), ("A", 0))),
    "Bh": ("Y", "fb", (("B", 0), ("h", 1)), (("s", 0), ("B", 0))),
    "Bk": ("Y", "fb", (("B", 0), ("k", 1)), (("B", 0),)),
    "M": ("X", "f", (("u", 1), ("B", 0), ("A", 1)), (("u", 0),)),
}


def reachable(initial):
    classes, index, edges = [], {}, set()

    def register(path):
        if path not in index:
            found, pending = {path}, [path]
            while pending:
                for other in stage.exchanges(pending.pop()):
                    if other not in found:
                        found.add(other)
                        pending.append(other)
            index.update((p, len(classes)) for p in found)
            classes.append(found)
        return index[path]

    register(initial)
    # Appending a newly discovered class extends the iterator's search frontier.
    for source, reps in enumerate(classes):
        for path in reps:
            for cut, word in enumerate(stage.slices("X", "f", path)):
                for name, (pole, base, src, dst) in prisms.items():
                    for pos in stage.sites("X", word, base, pole):
                        old = tuple((g, j + pos) for g, j in src)
                        if path[cut:cut + len(src)] == old:
                            new = tuple((g, j + pos) for g, j in dst)
                            target = register(path[:cut] + new + path[cut + len(old):])
                            edges.add((source, name, target))
    return classes, edges


def rank(path, n):
    marker = None
    depth = crossings = hidden = 0
    for word, (name, pos) in zip(stage.slices("X", "f", path), path):
        if name == "u":
            # Traversal order is right to left. H has a single lane.
            marker = sum(c in "fg" for c in word[pos:])
        elif name in ("s", "h"):
            depth += 1
        elif name in ("A", "B"):
            crossings += n + 1 - depth
        elif name == "k":
            hidden += 1
    assert depth == n and marker in (0, 1)
    return 1 - marker, crossings, hidden


def split_cup(n):
    initial = (("u", 1), ("B", 0), ("A", 1)) + (("s", 2),) * n
    classes, edges = reachable(initial)
    ranks = []
    for group in classes:
        values = {rank(p, n) for p in group}
        assert len(values) == 1
        ranks.append(values.pop())
    for src, _, dst in edges:
        assert ranks[src] > ranks[dst]

    # The incidence net retains both crossings and s while accumulating k.
    def fire(mark, name):
        _, _, src, dst = prisms[name]
        consumed = Counter(g for g, _ in src)
        assert consumed <= mark
        return mark - consumed + Counter(g for g, _ in dst)

    marking = Counter(g for g, _ in initial)
    for _ in range(2 * n):
        marking = fire(fire(marking, "As"), "Bh")
    for _ in range(2 * n):
        marking = fire(marking, "Bk")
    assert marking == Counter(g for g, _ in initial)
    print(f"n={n} states={len(classes)} moves={len(edges)} "
          f"largest erased count={max(r[2] for r in ranks)}")


def nonidentity_comparison(n):
    # The cone sends both the base edge and the transformation component to f.
    unary = Stage({"a": ("X", "X"), "f": ("X", "X")},
                  {"u": Rule("X", "f", "a"), "c": Rule("X", "fa", "af")})
    start = "f" * (n + 1)
    paths = list(unary.backwards("X", start, "a" + "f" * n, {"u"}, 1))
    classes, index = unary.quotient(paths)
    move = {"M": ("X", "ff", (("u", 1), ("c", 0)), (("u", 0),))}
    edges = unary.edges("X", start, classes, index, move)
    positions = [n - next(pos for g, pos in reps[0] if g == "u") for reps in classes]
    assert len(classes) == n + 1 and len(edges) == n
    assert all(positions[b] == positions[a] + 1 for a, _, b in edges)
    print(f"nonidentity comparison: {len(classes)} positions, {len(edges)} marker moves")


if __name__ == "__main__":
    for size in range(1, 5):
        split_cup(size)
    nonidentity_comparison(5)
