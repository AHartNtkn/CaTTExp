"""Check the finite disk contractions with one retained 4-update and up to three advances."""

from collections import Counter
from functools import cache
from itertools import permutations

from two_slot_interchange import moves


def check(a, b, varied):
    letters = [kind+str(i) for kind, size in [("A", a), ("B", b)] for i in range(1, size+1)]
    states = []
    for word in permutations(letters+["C"]):
        if any(list(filter(lambda x: x[0] == kind, word)) != sorted(x for x in word if x[0] == kind)
               for kind in "AB"):
            continue
        states += [word, tuple(x+"+" if x == varied else x for x in word)]
    edges = {w: [e for e in moves(w) if e.family != "globe" or w[e.lo] == varied] for w in states}
    rules = {w: set() for w in states}

    def add(w, name, lhs, rhs, symmetric=False):
        def finish(path):
            v = w
            for e in path:
                assert e in edges[v]
                v = e.apply(v)
            return v
        assert finish(lhs) == finish(rhs)
        rules[w].add((name, tuple(lhs), tuple(rhs)))
        if symmetric:
            rules[w].add((name, tuple(rhs), tuple(lhs)))

    for w in states:
        for first in edges[w]:
            middle = first.apply(w)
            for second in edges[middle]:
                end = second.apply(middle)
                if second.hi <= first.lo:
                    add(w, "exchange", [first, second], [second, first])
                if first.family == second.family and first.family in ("i", "r", "t"):
                    for direct in edges[w]:
                        if direct.family == first.family and direct.apply(w) == end:
                            add(w, "split", [direct], [first, second], symmetric=True)
                elif first.family == "h" and second.family == "i":
                    for direct in edges[w]:
                        if direct.family == "r" and direct.apply(w) == end:
                            add(w, "factor", [direct], [first, second], symmetric=True)
                if first.family not in ("h", "i") or second.family != "globe":
                    continue
                occurrence = next(i for i, x in enumerate(w) if x == varied)
                if not first.lo <= occurrence < first.hi:
                    continue
                update = next(e for e in edges[w] if e.family == "globe")
                changed = update.apply(w)
                moved = next(e for e in edges[changed] if e.family == first.family
                             and e.lo == first.lo and e.hi == first.hi)
                if first.family == "h":
                    if varied[0] == "B":
                        add(w, "right join variation", [update, moved], [first, second])
                else:
                    left_slot = "B" if first.hi <= w.index("C") else "A"
                    if varied[0] == left_slot:
                        add(w, "left naturality", [first, second], [update, moved])
                    else:
                        add(w, "right naturality", [update, moved], [first, second])

    @cache
    def paths(w):
        return ((),) + tuple((e,)+tail for e in edges[w] for tail in paths(e.apply(w)))

    counts = Counter()
    for w in states:
        words = paths(w)
        ids = {word: i for i, word in enumerate(words)}
        graph = [set() for _ in words]
        exchanges = set()
        for i, word in enumerate(words):
            current = w
            for at, e in enumerate(word):
                for name, lhs, rhs in rules[current]:
                    if word[at:at+len(lhs)] != lhs:
                        continue
                    dest = ids[word[:at]+rhs+word[at+len(lhs):]]
                    graph[i].add(dest)
                    counts[name] += 1
                    if name == "exchange":
                        exchanges.add((i, dest))
                current = e.apply(current)
        for src, dst in exchanges:
            seen = {dst}
            todo = [dst]
            while todo:
                nxt = graph[todo.pop()] - seen
                todo.extend(nxt)
                seen.update(nxt)
            assert src not in seen, (w, words[src], words[dst])
        counts["paths"] += len(words)
    return counts


if __name__ == "__main__":
    total = Counter()
    for a, b in [(2, 1), (1, 2)]:
        for k, size in [("A", a), ("B", b)]:
            for i in range(1, size+1):
                total.update(check(a, b, k+str(i)))
    print(dict(total))
