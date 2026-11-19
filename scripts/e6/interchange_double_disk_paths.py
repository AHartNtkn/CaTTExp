"""Decide proper degree-five exchanges on the complete binary (3,3) disk."""

from collections import Counter, defaultdict
from functools import cache
from itertools import permutations, product


def moves(state):
    word, x, y = state
    if x == 0:
        yield "x", (word, 1, y)
    if y == 0:
        yield "y", (word, x, 1)
    for name, before, after in (("r", "CA", "AC"), ("t", "BC", "CB"), ("h", "BCA", "ABC")):
        if before in word:
            yield name, (word.replace(before, after), x, y)
    i = word.index("C")
    for segment, before, after in [(word[:i], "AB", "BA"), (word[i+1:], "BA", "AB")]:
        if before in segment:
            yield "i", (word.replace(before, after), x, y)


def span(state, name):
    word = state[0]
    if name == "i":
        active = "AB" if "AB" in word else "BA"
    else:
        active = {"x": "A", "y": "B", "r": "CA", "t": "BC", "h": "BCA"}[name]
    lo = word.index(active)
    return lo, lo+len(active)


def build():
    states = [(s, x, y) for s in map("".join, permutations("ABC")) for x, y in product(range(2), repeat=2)]
    edges = {s: dict(moves(s)) for s in states}
    heights = {"BCA": 0, "CBA": 1, "CAB": 2, "ABC": 1, "BAC": 2, "ACB": 3}
    for s in states:
        assert all(heights[t[0]]+t[1]+t[2] > heights[s[0]]+s[1]+s[2] for t in edges[s].values())

    @cache
    def walks(start):
        return ((),) + tuple((label,)+suffix for label, nxt in edges[start].items() for suffix in walks(nxt))

    rules = defaultdict(list)
    def endpoint(start, names):
        for letter in names:
            start = edges[start][letter]
        return start

    def add(s, name, lhs, rhs):
        assert endpoint(s, lhs) == endpoint(s, rhs)
        rules[s].append((name, tuple(lhs), tuple(rhs)))

    for s in states:
        word, x, y = s
        for early, late in permutations(edges[s], 2):
            if span(s, early)[1] <= span(s, late)[0]:
                add(s, "exchange", late+early, early+late)
        if word == "BCA":
            add(s, "expand", "r", "hi")
            add(s, "contract", "hi", "r")
            if not y:
                add(s, "right join variation", "yh", "hy")
        if "i" in edges[s]:
            left, right = ("y", "x") if word.endswith("C") else ("x", "y")
            if left in edges[s]:
                add(s, "left naturality", "i"+left, left+"i")
            if right in edges[s]:
                add(s, "right naturality", right+"i", "i"+right)
            if not x and not y:
                add(s, "shifted join", right+"i"+left, left+right+"i")

    paths = [(s, w) for s in states for w in walks(s)]
    ids = {path: i for i, path in enumerate(paths)}
    graph = [set() for _ in paths]
    designated = set()
    counts = Counter()
    for i, (start, word) in enumerate(paths):
        state = start
        for at, letter in enumerate(word):
            for name, left, right in rules[state]:
                if word[at:at+len(left)] != left:
                    continue
                target = ids[start, word[:at] + right + word[at+len(left):]]
                graph[i].add(target)
                counts[name] += 1
                if name == "exchange":
                    designated.add((i, target))
            state = edges[state][letter]
    return paths, graph, designated, counts


def check():
    paths, graph, designated, counts = build()
    for start, end in designated:
        seen = {end}
        todo = [end]
        while todo:
            current = todo.pop()
            for target in graph[current] - seen:
                seen.add(target)
                todo.append(target)
        assert start not in seen, (paths[start], paths[end])
    print(f"Enumerated {len(paths)} contextual 4-paths and {sum(counts.values())} directed rewrites.")
    print(f"All {len(designated)} proper contextual atomic exchanges lack a reverse; "
          f"the graph includes {counts['shifted join']} shifted joins and "
          f"{counts['right join variation']} right join variations.")


if __name__ == "__main__":
    check()
