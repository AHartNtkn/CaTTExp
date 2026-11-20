"""Find small transfer obstructions by matching and compile SAT into controls."""

from itertools import combinations, combinations_with_replacement, product

from homotopy_polygraph_transfer_graph import components, obstruction, transfer_options


def match_processes(pattern, available):
    """Assign each requested edge slot to a different process."""
    owner = {}
    def augment(slot, tried):
        for process in available[pattern[slot]]:
            if process in tried:
                continue
            tried.add(process)
            if process not in owner or augment(owner[process], tried):
                owner[process] = slot
                return True
        return False
    if all(augment(slot, set()) for slot in range(len(pattern))):
        return [(process, pattern[slot]) for process, slot in owner.items()]
    return None


def small_obstruction(graphs):
    available = {}
    for i, graph in enumerate(graphs):
        for edge in transfer_options(graph):
            available.setdefault(edge, []).append(i)
    resources = sorted({v for edge in available for v in edge})
    for size in range(2, min(len(resources), len(graphs) - 2) + 1):
        for group in combinations(resources, size):
            vertices = frozenset(group)
            internal = [e for e in available if set(e) <= vertices]
            for pattern in combinations_with_replacement(internal, size + 2):
                if components(pattern) == {vertices}:
                    witness = match_processes(pattern, available)
                    if witness is not None:
                        return witness
    return None


def control(choices):
    # Distinct control branches share only their initial vertex.
    return [edge for j, (r, s) in enumerate(choices) for edge in
            [(0, ('P', r), 2*j + 1), (2*j + 1, ('V', s), 2*j + 2)]]


def compile_cnf(variables, clauses):
    """Make a coloured acyclic source-target graph plus three return arcs."""
    options = {}
    vertex = 1
    def fresh():
        nonlocal vertex
        v = vertex
        vertex += 1
        return v
    def arc(source, target, colour=None):
        if colour is None:
            colour = ('private', len(options))
        options.setdefault(colour, []).append((source, target))
    start = current = 0
    for variable in range(1, variables + 1):
        target = fresh()
        for false_literal in (variable, -variable):
            node = current
            for c, clause in enumerate(clauses):
                for j, literal in enumerate(clause):
                    if literal == false_literal:
                        after = fresh()
                        arc(node, after, (c, j))
                        node = after
            arc(node, target)
        current = target
    for c, clause in enumerate(clauses):
        target = fresh()
        for j in range(len(clause)):
            arc(current, target, (c, j))
        current = target
    for _ in range(3):
        arc(current, start)
    assert all(len(opts) <= 2 for opts in options.values())
    return [control(opts) for opts in options.values()]


def check():
    arcs = [(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)]
    choices = [control([]), control(arcs[:1]), control(arcs[:2]),
               control(arcs[2:4]), control(arcs[4:]), control(arcs[::2])]
    cases = 0
    for family in combinations_with_replacement(range(len(choices)), 5):
        graphs = [choices[i] for i in family]
        matched = small_obstruction(graphs)
        assert bool(matched) == bool(obstruction(graphs))
        if matched:
            assert len({i for i, _ in matched}) == len(matched)
            assert all(e in transfer_options(graphs[i]) for i, e in matched)
            vertices = set().union(*(e for _, e in matched))
            assert len(matched) == len(vertices) + 2
        cases += 1
    print(f'{cases} branching graph families agree by matching and choice enumeration.')

    literals = (1, -1, 2, -2)
    clause_types = [(i,) for i in literals] + list(combinations(literals, 2))
    checked = bad = 0
    for clauses in combinations_with_replacement(clause_types, 3):
        graphs = compile_cnf(2, clauses)
        sat = any(all(any(bits[abs(x)-1] == (x > 0) for x in c) for c in clauses)
                  for bits in product([False, True], repeat=2))
        # The direct solver tries individual processes' available control branches.
        assert bool(obstruction(graphs)) == sat, clauses
        checked += 1
        bad += not sat
    print(f'{checked} CNFs checked at the control-graph level, including {bad} unsatisfiable.')


if __name__ == '__main__':
    check()
