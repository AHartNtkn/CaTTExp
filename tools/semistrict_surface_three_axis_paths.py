"""Enumerate old Gray 3-faces between the temporal ends of a three-axis chart."""
import argparse
from collections import Counter, defaultdict, deque
from itertools import product
from typing import NamedTuple

from semistrict_surface_return_gaps import exchange_at
from semistrict_surface_scalar_cube import check_cube


class Chart(NamedTuple):
    rules: tuple  # spatial order, each entry is (name, input edge word, output edge word)
    gaps: tuple

    def reading(self, order):
        done = set()
        steps = []
        for i in order:
            prefix = sum(len(self.gaps[j]) for j in range(i))
            for j, (_, before, after) in enumerate(self.rules[:i]):
                prefix += len(after if j in done else before)
            steps.append((prefix, self.rules[i][0]))
            done.add(i)
        return tuple(steps)

    def start_word(self):
        return ''.join(rule[1] + gap for rule, gap in zip(self.rules, (*self.gaps, ''), strict=True))


def exchange_graph(chart):
    """Read contextual generating squares, retaining their temporal position."""
    marks = {name: (s, t) for name, s, t in chart.rules}
    if any(marks[name] != (s, t) for name, s, t in chart.rules):
        raise ValueError('one generator name must have one attaching pair')
    # A directed square executes the spatially left rewrite first.
    graph = defaultdict(list)
    source = chart.reading((2, 1, 0))
    target = chart.reading((0, 1, 2))
    seen = {source}
    pending = deque(seen)
    while pending:
        history = pending.popleft()
        for pos in range(len(history) - 1):
            moved = exchange_at(history, pos, marks)
            if moved is None:
                continue
            graph[history].append((pos + 1, moved))
            if moved not in seen:
                seen.add(moved)
                pending.append(moved)
    return source, target, graph


def corridor(source, target, graph):
    """Keep precisely states on a path to target in the source-reachable graph."""
    incoming = defaultdict(set)
    for state, arrows in graph.items():
        for pos, dest in arrows:
            incoming[dest].add(state)
    live = {target}
    pending = list(live)
    while pending:
        for state in incoming[pending.pop()] - live:
            live.add(state)
            pending.append(state)
    graph = {state: [(p, dest) for p, dest in graph.get(state, ()) if dest in live] for state in live}
    indegree = Counter(dest for arrows in graph.values() for _, dest in arrows)
    queue = deque(state for state in live if not indegree[state])
    order = []
    while queue:
        state = queue.popleft()
        order.append(state)
        for _, dest in graph[state]:
            indegree[dest] -= 1
            if not indegree[dest]:
                queue.append(dest)
    if len(order) != len(live):
        return graph, None
    counts = Counter({source: 1})
    for state in order:
        for _, dest in graph[state]:
            counts[dest] += counts[state]
    return graph, counts[target]


def check_chart(chart):
    source, target, graph = exchange_graph(chart)
    for word in ('121', '212'):
        state = source
        for letter in word:
            state = dict(graph[state])[int(letter)]
        assert state == target
    return corridor(source, target, graph)


def check():
    counts = Counter()
    # Independently check each retained edge by splitting an actual spatial word.
    check_cube()
    for sizes in product(range(4), repeat=3):
        letters = tuple(('abcd'[i], 'f' * (i // 2), 'f' * (i % 2)) for i in sizes)
        for gaps in product(('', 'f'), repeat=2):
            chart = Chart(letters, gaps)
            graph, count = check_chart(chart)
            counts['charts'] += 1
            counts['cyclic' if count is None else f'{count} paths'] += 1
            if all(s for _, s, _ in letters) or all(t for _, _, t in letters) or all(gaps):
                assert count == 2
                assert len(graph) == 6 and sum(map(len, graph.values())) == 6
                counts['separated'] += 1
            start = chart.start_word()
            for state, arrows in graph.items():
                # Replay on a spatial edge string. Enumerate each elementary square
                # by splitting the current word into prefix, two sources, gap, suffix.
                path = start
                expected = []
                marks = {n: (s, t) for n, s, t in letters}
                for i, (at, name) in enumerate(state):
                    s, t = marks[name]
                    assert 0 <= at <= len(path) and path[at:at+len(s)] == s
                    if i + 1 < len(state):
                        nxt, other = state[i+1]
                        ls, lt = marks[other]
                        for p in range(len(path)+1):
                            for end in range(p + len(ls), len(path)+1):
                                if (p != nxt or end != at or not path.startswith(ls, p)
                                        or not path.startswith(s, end)):
                                    continue
                                new = state[:i] + ((p, other), (end+len(lt)-len(ls), name)) + state[i+2:]
                                if new in graph:
                                    expected.append((i+1, new))
                    path = path[:at] + t + path[at+len(s):]
                assert set(expected) == set(arrows)
                counts['states replayed'] += 1
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--chart', nargs=3, metavar='NAME:SOURCE:TARGET')
    parser.add_argument('--gaps', nargs=2, default=('', ''))
    args = parser.parse_args()
    if args.chart:
        records = tuple(tuple(r.split(':')) for r in args.chart)
        if any(len(r) != 3 or not r[0] for r in records):
            parser.error('each axis needs a name, source word, and target word')
        graph, count = check_chart(Chart(records, tuple(args.gaps)))
        print(f'{len(graph)} histories, {sum(map(len, graph.values()))} exchange edges')
        print('infinitely many parallel crossing paths' if count is None else f'{count} parallel crossing paths')
    else:
        for key, val in sorted(check().items()):
            print(f'{val:,} {key}')


if __name__ == '__main__':
    main()
