"""Finite long hom of the marked crossing model in Researcher Response 1 (r5)."""

from collections import Counter
from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Path:
    start: tuple[int, int]
    word: str

    @property
    def end(self):
        i, j = self.start
        return i + self.word.count("A"), j + self.word.count("B")

    def then(self, other):
        assert self.end == other.start
        return Path(self.start, self.word + other.word)

    def successors(self):
        for k in range(len(self.word) - 1):
            if self.word[k:k + 2] == "BA":
                yield Path(self.start, self.word[:k] + "AB" + self.word[k + 2:])


def reachable(path):
    found, pending = {path}, [path]
    while pending:
        for nxt in pending.pop().successors():
            if nxt not in found:
                found.add(nxt)
                pending.append(nxt)
    return found


@dataclass(frozen=True)
class Cell:
    source: Path
    target: Path
    tag: frozenset

    def vertical(self, other):
        assert self.target == other.source
        return Cell(self.source, other.target, self.tag | other.tag)

    def horizontal(self, other):
        return Cell(self.source.then(other.source), self.target.then(other.target),
                    self.tag | other.tag)


def identity(path):
    return Cell(path, path, frozenset())


def square(start, a, b):
    source = Path(start, "B" * b + "A" * a)
    target = Path(start, "A" * a + "B" * b)
    tag = frozenset({(a, b)}) if a and b else frozenset()
    return Cell(source, target, tag)


def check():
    paths = set()
    for i, j in product(range(2), range(3)):
        for n in range(4):
            for letters in product("AB", repeat=n):
                path = Path((i, j), "".join(letters))
                if path.end[0] <= 1 and path.end[1] <= 2:
                    paths.add(path)
    forward = {p: reachable(p) for p in paths}
    tags = (frozenset(), frozenset({(1, 1)}), frozenset({(1, 2)}),
            frozenset({(1, 1), (1, 2)}))
    cells = {Cell(p, q, tag) for p in paths for q in forward[p] for tag in tags}

    vertical_pairs = []
    for x, y in product(cells, repeat=2):
        if x.target == y.source:
            assert x.vertical(y) in cells
            vertical_pairs.append((x, y))
        if x.source.end == y.source.start:
            assert x.horizontal(y) in cells

    # Both dimensions of composition are available on the entire grid.
    # Check every square of composable pairs, including nonempty identity-base tags.
    rectangles = 0
    for (x, y), (u, v) in product(vertical_pairs, repeat=2):
        if x.source.end == u.source.start:
            assert x.vertical(y).horizontal(u.vertical(v)) == x.horizontal(u).vertical(y.horizontal(v))
            rectangles += 1

    status = Counter()
    for i, j in product(range(2), range(3)):
        for a, b in product(range(2 - i), range(3 - j)):
            cell = square((i, j), a, b)
            assert cell in cells
            if a and b:
                assert cell.source not in forward[cell.target]
                status["proper"] += 1
            else:
                assert cell == identity(cell.source)
                status["unit"] += 1

    direct = square((0, 0), 1, 2)
    first = identity(Path((0, 0), "B")).horizontal(square((0, 1), 1, 1))
    second = square((0, 0), 1, 1).horizontal(identity(Path((1, 1), "B")))
    expanded = first.vertical(second)
    assert (direct.source, direct.target) == (expanded.source, expanded.target)
    assert direct.tag == {(1, 2)} and expanded.tag == {(1, 1)}
    print(f"{len(paths)} paths, {len(cells)} decorated 2-cells, {rectangles} interchange rectangles.")
    print(f"{status['proper']} directed and {status['unit']} unit squares.")
    print("The direct and expanded squares both run BBA to ABB and have distinct tags.")


if __name__ == "__main__":
    check()
