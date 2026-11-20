"""Certify forced cubical colour pairs from all labelled facet-omission trees."""
from argparse import ArgumentParser
from itertools import combinations, product

from relative_coherence_polarized_cube import vertex_names
from relative_coherence_simplex_carrier import flags, orientation


def tree_from_prufer(code):
    n = len(code)+2
    deg = [1+code.count(i) for i in range(n)]
    adj = [set() for _ in range(n)]
    def edge(i, j):
        adj[i].add(j)
        adj[j].add(i)
        deg[i] -= 1
        deg[j] -= 1
    for j in code:
        i = deg.index(1)
        edge(i, j)
    edge(*(i for i, d in enumerate(deg) if d == 1))
    return adj


def corridor(adj, i, j):
    parent = {i: None}
    stack = [i]
    while stack:
        u = stack.pop()
        for v in adj[u] - parent.keys():
            parent[v] = u
            stack.append(v)
    # Orient away from i, selecting the arrowhead as the omission.
    incoming = [int(u != i) for u in range(len(adj))]
    orientation = {(u, p) for u, p in parent.items() if p is not None}
    interior = []
    v = j
    while v != i:
        u = parent[v]
        incoming[v] -= 1
        assert {k for k, d in enumerate(incoming) if not d} == {i, j}
        orientation.remove((v, u))
        orientation.add((u, v))
        incoming[u] += 1
        if u != i:
            interior.append(frozenset(orientation))
        allowed = {k for k, d in enumerate(incoming) if not d}
        assert allowed == ({j} if u == i else {i, j})
        v = u
    return interior


def check(max_names):
    for n in range(2, max_names+1):
        count = 0
        for code in product(range(n), repeat=n-2):
            adj = tree_from_prufer(code)
            interiors = set()
            for i, j in combinations(range(n), 2):
                inner = corridor(adj, i, j)
                assert not interiors.intersection(inner)
                interiors.update(inner)
                count += 1
        names = vertex_names(n, range(1, n))
        edges = {(x, names[mask | (1 << j)]) for mask, x in enumerate(names)
                 for j in range(n-1) if not mask & (1 << j)}
        pairs = {(i, j) for i, j in edges if i != j}
        assert pairs == {(i, j) for i in range(1, n+1) for j in range(1, i)}
        degree = 0
        for path, sign in flags(range(n-1)):
            values = [names[i] for i in path]
            if len(set(values)) == n:
                degree += sign * orientation(values)
        assert abs(degree) == 1
        print(f'{n} colours: {count} forced-pair paths; {len(pairs)} directed nonconstant '
              f'edge types in the minimum colouring, degree {degree}.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('names', type=int, default=6, nargs='?')
    check(parser.parse_args().names)
