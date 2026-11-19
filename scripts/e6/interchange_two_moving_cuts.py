"""Certify temporal exchanges with a common event cut on the two-advance-per-slot arity.

A separate integer rank is computed on 4-paths out of each 3-history.
The last pass checks the rank against every legal rewrite in the presentation.
"""
from collections import Counter, defaultdict

from interchange_reachability import Path, Presentation, solve, verify
from interchange_two_moving import Move, ground, ground_all, walk


def progress(history):
    """Lexicographic progress of 4-edges, proving that all raw paths are finite."""
    incident = history[:history.index('a')].count('X') + history[:history.index('b')].count('Y')
    in_left = 0
    ordered = 0
    for event in history:
        if event in 'aX':
            in_left += 1
        else:
            ordered += in_left
    return incident, ordered


def all_paths(start, outgoing):
    paths = []
    pending = [(start, ())]
    while pending:
        history, edges = pending.pop()
        paths.append(Path(start, edges))
        pending.extend((after, edges + (name,)) for name, after in outgoing[history])
    return paths


def component_ranks(graph):
    """Number strongly connected components in topological order (Kosaraju)."""
    back = [[] for _ in graph]
    for src, row in enumerate(graph):
        for dst in row:
            back[dst].append(src)
    seen = set()
    finished = []
    for i in range(len(graph)):
        if i in seen:
            continue
        seen.add(i)
        stack = [(i, iter(graph[i]))]
        while stack:
            src, neighbors = stack[-1]
            dst = next(neighbors, None)
            if dst is None:
                finished.append(src)
                stack.pop()
            elif dst not in seen:
                seen.add(dst)
                stack.append((dst, iter(graph[dst])))
    ranks = [-1] * len(graph)
    label = 0
    for i in reversed(finished):
        if ranks[i] >= 0:
            continue
        ranks[i] = label
        todo = [i]
        while todo:
            for j in back[todo.pop()]:
                if ranks[j] < 0:
                    ranks[j] = label
                    todo.append(j)
        label += 1
    return ranks


def certify(m, n):
    presentation, moves = ground_all(m, n)
    outgoing = defaultdict(list)
    for name, edge in presentation.edges.items():
        if progress(edge.target) <= progress(edge.source):
            raise ValueError(f'4-edge failed to make progress: {name}')
        outgoing[edge.source].append((name, edge.target))
    kinds = {name: name.split()[0] for name in presentation.rules}
    delta_cuts = {}
    for name, rule in presentation.rules.items():
        if kinds[name] == 'delta':
            later, earlier = (moves[e] for e in rule.source.edges)
            delta_cuts[name] = sum(1 << k for k in range(earlier.hi, later.lo+1))
    # Prefixes of the same length coincide as event sets iff their counts
    # agree: repeated X or Y events occur in their generating order.
    prefix = {w: [tuple(w[:k].count(c) for c in "abXY") for k in range(len(w)+1)]
              for w in presentation.vertices}
    def common_cuts(u, v):
        return sum(1 << k for k, (a, b) in enumerate(zip(prefix[u], prefix[v])) if a == b)
    agree = {(u, v): common_cuts(u, v) for u in prefix for v in prefix}
    totals = Counter()
    for start in sorted(presentation.vertices):
        paths = all_paths(start, outgoing)
        ids = {p: i for i, p in enumerate(paths)}
        graph = [[ids[q] for _, q in presentation.successors(p)] for p in paths]
        ranks = component_ranks(graph)
        totals['4-paths'] += len(paths)
        for i, p in enumerate(paths):
            outside = agree[start, presentation.end(p)]
            for step, q in presentation.successors(p):
                kind = kinds[step.rule]
                difference = ranks[ids[q]] - ranks[i]
                if kind == 'delta':
                    middle = presentation.edges[p.edges[step.offset]].source
                    globular_cut = bool(outside & agree[start, middle] & delta_cuts[step.rule])
                else:
                    globular_cut = False
                if globular_cut:
                    totals['shared boundary cut delta'] += 1
                if kind == 'delta' and difference == 0:
                    totals['returning delta without a cut'] += 1
                if difference < int(globular_cut):
                    if kind == 'delta' and difference == 0:
                        reverse = solve(presentation, q, p)
                        if reverse.reachable and verify(presentation, q, p, reverse):
                            raise ValueError(f'reverse found for {p} -> {q}: {reverse.steps}')
                    raise ValueError(f'rank failed for {step} at {p}')
                totals[kind] += 1
    print(f'({m},{n}) {len(presentation.vertices)} histories, {len(presentation.edges)} 4-edges, '
          f'{len(presentation.rules)} rules. Checked {totals["4-paths"]} raw 4-paths.')
    print('Contextual applications:', dict(sorted((k, v) for k, v in totals.items() if k != '4-paths')))
    return totals


def check_straddling_context():
    # Both the prefix and suffix are mixed. The wide r in the prefix crosses
    # both a and b, so it cannot be assigned to either input of the time cut.
    start = 'aXbYYY'
    presentation, _ = ground(start, 'XaYYYb')
    before = (Move('r', 0, 1, 2), Move('r', 1, 3, 4))
    early = Move('i', 1, 2, 3)
    late = Move('r', 3, 4, 5)
    after = (Move('r', 4, 5, 6),)
    lhs = walk(start, before + (late, early) + after)
    rhs = walk(start, before + (early, late) + after)
    assert lhs != rhs and presentation.end(lhs) == presentation.end(rhs) == 'XaYYYb'
    assert any(q == rhs and step.rule.startswith('delta ')
               for step, q in presentation.successors(lhs))
    equations = Presentation(presentation.vertices, presentation.edges,
                             [r for r in presentation.rules.values() if r.equation])
    back = solve(equations, rhs, lhs)
    assert back.reachable and verify(equations, rhs, lhs, back)
    print('Straddling mixed context, return by equations:',
          [step.rule.split()[0] for step in back.steps])


if __name__ == '__main__':
    check_straddling_context()
    census = certify(2, 2)
    assert census['4-paths'] == 191_280 and census['shared boundary cut delta'] == 2_887
