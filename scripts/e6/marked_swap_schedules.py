"""Check 6-dimensional comparisons in the shifted marked-word evaluation."""

from collections import defaultdict
from functools import cache
from itertools import product


def occurrences(raw):
    counts = {"E": 0, "L": 0}
    result = []
    for letter in raw:
        counts[letter] += 1
        result.append(counts[letter] if letter == "E" else -counts[letter])
    return tuple(result)


def moves(word):
    for i, (left, right) in enumerate(zip(word, word[1:])):
        if left < 0 < right:
            yield (right, -left), word[:i] + (right, left) + word[i + 2:]


@cache
def schedules(start, end):
    if start == end:
        return ((),)
    result = []
    for event, after in moves(start):
        e, l = event
        if end.index(e) < end.index(-l):
            result.extend((event,) + tail for tail in schedules(after, end))
    return tuple(result)


@cache
def expansions(es, ls):
    if len(es) == len(ls) == 1:
        return {((es[0], ls[0]),)}
    result = set()
    for i in range(1, len(es)):
        result.update(p + q for p in expansions(es[:i], ls) for q in expansions(es[i:], ls))
    for i in range(1, len(ls)):
        result.update(p + q for p in expansions(es, ls[i:]) for q in expansions(es, ls[:i]))
    return result


@cache
def block_rules(word):
    rules = []
    for middle in range(1, len(word)):
        left, right = middle, middle
        while left > 0 and word[left - 1] < 0:
            left -= 1
        while right < len(word) and word[right] > 0:
            right += 1
        for i in range(left, middle - 1):
            for j in range(middle + 2, right + 1):
                rules.append(expansions(word[middle:j], tuple(-x for x in word[i:middle])))
    return rules


def table(start, end):
    paths = schedules(start, end)
    parent = {p: p for p in paths}

    def root(p):
        while parent[p] != p:
            parent[p] = parent[parent[p]]
            p = parent[p]
        return p

    exchange = []
    for path in paths:
        state = start
        for i, event in enumerate(path):
            for rect in block_rules(state):
                length = len(next(iter(rect)))
                if path[i:i + length] in rect:
                    for other in rect:
                        replacement = path[:i] + other + path[i + length:]
                        parent[root(replacement)] = root(path)
            enabled = dict(moves(state))
            if i + 1 < len(path) and path[i + 1] in enabled:
                other = path[i + 1]
                if state.index(event[0]) > state.index(other[0]):
                    exchange.append((path, path[:i] + (other, event) + path[i + 2:]))
            state = enabled[event]
        assert state == end
    graph = defaultdict(set)
    for p, q in exchange:
        graph[root(p)].add(root(q))
    return {p: root(p) for p in paths}, graph


def reachable(start, graph):
    seen, pending = {start}, [start]
    while pending:
        fresh = graph[pending.pop()] - seen
        seen.update(fresh)
        pending.extend(fresh)
    return seen


def check():
    comparisons = intervals = 0
    for length in range(4, 8):
        words = [occurrences(raw) for raw in product("EL", repeat=length)]
        for start in words:
            for end in words:
                if set(start) != set(end):
                    continue
                cuts = []
                for h in range(2, length - 1):
                    if set(start[:h]) != set(end[:h]):
                        continue
                    a, b = schedules(start[:h], end[:h]), schedules(start[h:], end[h:])
                    if a and b and a[0] and b[0]:
                        cuts.append((a, b))
                if not cuts:
                    continue
                intervals += 1
                classes, graph = table(start, end)
                closure = {x: reachable(x, graph) for x in set(classes.values())}
                for left, right in cuts:
                    for x, y in product(left, right):
                        source = classes[y + x]
                        for i in range(1, len(x) + 1):
                            for j in range(len(y)):
                                dest = classes[y[:j] + x[:i] + y[j:] + x[i:]]
                                assert dest in closure[source] and source not in closure[dest]
                                comparisons += 1
    print(f"Checked {comparisons} proper rectangles on {intervals} marked word intervals.")

    for initial, final, expected in (("LELE", "ELEL", 2), ("LLEE", "EELL", 1)):
        classes, _ = table(occurrences(initial), occurrences(final))
        assert len(classes) == 2 and len(set(classes.values())) == expected
        print(f"{initial} to {final}: two schedules in {expected} block-equation class(es).")

    for initial, final in (("LELELELE", "ELELLELE"), ("ELELLELE", "ELELELEL")):
        classes, graph = table(occurrences(initial), occurrences(final))
        assert len(set(classes.values())) == 2
        assert sum(len(edges) for edges in graph.values()) == 1
    print("Both consecutive inputs of the degree-seven thinness test remain directed.")


if __name__ == "__main__":
    check()
