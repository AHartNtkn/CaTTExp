"""Find first-event obstructions and compile the finite no-triple square-return test.

JSON uses single-character edge keys with pairs of vertices, named 2-cell marks
with pairs of nonempty edge words, and rules with path, source and target.
Each step is [zero-based spatial position, mark].
"""

from argparse import ArgumentParser
from collections import Counter, deque
from itertools import product
import json
from pathlib import Path

from semistrict_surface_return_gaps import Presentation, Rule, gap_outside_dictionary


def occurrences(path, subword):
    for i in range(len(path) - len(subword) + 1):
        if path.startswith(subword, i):
            yield i


def first_event_graph(pres, path):
    nodes = {(i, name) for name, (source, _) in pres.marks.items()
             for i in occurrences(path, source)}
    graph = {node: set() for node in nodes}
    for right in nodes:
        graph[right].update(left for left in nodes
                            if left[0] + len(pres.marks[left[1]][0]) <= right[0])
    for rule in pres.rules:
        (i, a), (j, b) = rule.source[0], rule.target[0]
        for off in occurrences(path, rule.path):
            graph[off + i, a].add((off + j, b))
    return graph


def accessible(graph, first):
    seen, queue = {first}, deque([first])
    while queue:
        for node in graph[queue.popleft()] - seen:
            seen.add(node)
            queue.append(node)
    return seen


def obligations(pres):
    vertices = {v for poles in pres.edges.values() for v in poles}
    reach = {v: {v} for v in vertices}
    for s, t in pres.edges.values():
        reach[s].add(t)
    for v in vertices:
        for s in vertices:
            if v in reach[s]:
                reach[s].update(reach[v])
    pairs = [(a, b) for a, b in product(pres.marks, repeat=2)
             if pres.poles(pres.marks[b][0])[0] in reach[pres.poles(pres.marks[a][0])[1]]]
    for a, b in pairs:
        for c in pres.marks:
            if (b, c) in pairs:
                return {'spatial_triple': [a, b, c]}
    dictionary = {''} | {rule.path[i:j] for rule in pres.rules
                          for i in range(len(rule.path)) for j in range(i + 1, len(rule.path) + 1)}
    required = []
    for a, b in pairs:
        s, t = pres.poles(pres.marks[a][0])[1], pres.poles(pres.marks[b][0])[0]
        missing = gap_outside_dictionary(pres.edges, s, t, dictionary)
        if missing is not None:
            case = pres.square(a, missing, b)
            assert case[2][0] not in accessible(first_event_graph(pres, case[0]), case[1][0])
            return {'impossible_gap': [a, missing, b]}
        for gap in sorted(dictionary):
            matches = pres.poles(gap) == (s, t) if gap else s == t
            if matches:
                required.append((a, gap, b))
    for a, gap, b in required:
        path, lr, rl = pres.square(a, gap, b)
        if rl[0] not in accessible(first_event_graph(pres, path), lr[0]):
            return {'impossible_first_event': [a, gap, b]}
    return {'required_returns': required}


def checks():
    totals = Counter()
    edges = {'f': (0, 1), 'h': (1, 1), 'g': (1, 2)}
    marks = {'a': ('f', 'f'), 'c': ('fh', 'f'), 'd': ('f', 'fh'), 'b': ('g', 'g')}
    bare = Presentation(edges, marks, [])
    local = Rule('fh', ((0, 'a'),), ((0, 'c'), (0, 'a'), (0, 'd')))
    rules = [local, Rule(local.path, local.target, local.source)]
    for a in ('a', 'c', 'd'):
        rules.append(Rule(*bare.square(a, '', 'b')))
    pres = Presentation(edges, marks, rules)
    assert 'impossible_gap' in obligations(pres)
    for n in range(2, 20):
        path, lr, rl = bare.square('a', 'h' * n, 'b')
        allowed = accessible(first_event_graph(pres, path), lr[0])
        assert rl[0] not in allowed
        reading = lr
        for k in range(n):
            reading = next(r for r, info in pres.moves(path, reading)
                           if info is not None and info[:2] == (local, k))
        assert 'fg' in pres.walk(path, reading) and reading[0] in allowed
        totals['entire middle path consumed inside a history'] += 1
    for n in range(4):
        path, lr, rl = pres.square('a', 'h' * n, 'b')
        first_graph = first_event_graph(pres, path)
        frontier = pres.reachable(path, lr, 9) | pres.reachable(path, rl, 9)
        for reading in frontier:
            for successor, _ in pres.moves(path, reading):
                assert reading[0] == successor[0] or successor[0] in first_graph[reading[0]]
                totals['literal moves projected to the first-event graph'] += 1

    # Branching finite middle graph with local length-changing rules on both
    # sides. Every choice of bridge rules has its independent ground truth.
    edges = {'f': (0, 1), 'h': (1, 2), 'k': (1, 2), 'g': (2, 3)}
    marks = {'a': ('f', 'f'), 'b': ('g', 'g')}
    original = Presentation(edges, marks, [])
    short = [Rule('f', ((0, 'a'),), ((0, 'a'), (0, 'a'))),
             Rule('g', ((0, 'b'), (0, 'b')), ((0, 'b'),))]
    for use_h, use_k in product((True, False), repeat=2):
        selected = [gap for gap, active in [('h', use_h), ('k', use_k)] if active]
        instance = Presentation(edges, marks, short + [Rule(*original.square('a', gap, 'b')) for gap in selected])
        result = obligations(instance)
        if use_h and use_k:
            assert set(result['required_returns']) == {('a', g, 'b') for g in selected}
            for case in result['required_returns']:
                path, lr, rl = instance.square(*case)
                assert rl in instance.reachable(path, lr, 2)
        else:
            assert result['impossible_gap'][1] not in selected
        totals['finite return compilations'] += 1
    for key, count in sorted(totals.items()):
        print(f'{count:,} {key}')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path)
    args = parser.parse_args()
    if args.base:
        data = json.loads(args.base.read_text())
        rules = [Rule(r['path'], tuple(map(tuple, r['source'])), tuple(map(tuple, r['target'])))
                 for r in data['rules']]
        print(json.dumps(obligations(Presentation(data['edges'], data['marks'], rules))))
    else:
        checks()
