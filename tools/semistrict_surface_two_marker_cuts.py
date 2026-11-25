"""Find cuts detecting both sheets of every circular two-event chart in a finite search."""
from collections import Counter, defaultdict

from relative_coherence_local_links import Circuits, FACES
from semistrict_surface_shared_edge import braid_image


def paths(diagrams, frontier, markers):
    # Recover precisely the gates of this circuit, excluding gates created while
    # enumerating other diagrams with the same input word.
    consumer = {}
    seen = set()
    stack = list(frontier)
    while stack:
        wire = stack.pop()
        if wire < 0:
            continue
        node, _ = diagrams.producers[wire]
        if node in seen:
            continue
        seen.add(node)
        for i, port in enumerate(node[1]):
            consumer[port] = node, i
            stack.append(port)

    idle = {}
    for node in markers:
        name, ports = node
        outs = [diagrams.apply(g, pos, ports) for g, pos in diagrams.faces[name]]
        idle[node] = {(i,j) for i, p in enumerate(ports) for j, q in enumerate(outs[0])
                      if p == q == outs[1][j]}
    for initial, port in enumerate(diagrams.inputs):
        todo = [(port, ())]
        while todo:
            current, trace = todo.pop()
            if current not in consumer:
                if sum(node in idle for node, _, _ in trace) == 2:
                    yield initial, trace, frontier.index(current)
                continue
            node, i = consumer[current]
            for j, out in enumerate(diagrams.outputs[node]):
                if node not in idle or (i,j) in idle[node]:
                    todo.append((out, trace + ((node,i,j),)))


def sides(diagrams, frontier, first, second):
    marks = (first, second)
    return (diagrams.expand(frontier, dict.fromkeys(marks, 0), (first,)),
            diagrams.expand(frontier, dict.fromkeys(marks, 1), (second,)))


def records(diagrams, frontier, marks, flip):
    for start, trace, end in paths(diagrams, frontier, marks):
        visited = [node for node, _, _ in trace if node in marks]
        oriented = marks[::-1] if flip else marks
        sign = 1 if visited == oriented else -1

        def side(omit):
            return start, tuple((node[0], i, j) for node, i, j in trace if node != omit), end

        # Same four one-marker circuits, with the same cuts on each. An erased
        # marker contributes no ordinary gate on its chosen idle wire.
        keys = tuple(side(m) for m in (oriented[1], oriented[0], oriented[0], oriented[1]))
        yield keys, sign


def audit(bound):
    rules = {k: FACES[k] for k in 'UABVW'}
    rules['A'] = rules['A'][::-1]
    diagrams = Circuits(5, rules)
    frames = defaultdict(list)
    for frontier, marks in diagrams.enumerate(bound):
        if len(marks) == 2:
            ab, ba = sides(diagrams, frontier, *marks), sides(diagrams, frontier, *marks[::-1])
            pair = tuple(sorted((ab, ba)))
            frames[pair].append((frontier, marks, ab != pair[0]))

    circles = paths_checked = 0
    for charts in frames.values():
        if len(charts) == 1:
            continue
        assert len(charts) == 2
        first, second = [set(records(diagrams, *chart)) for chart in charts]
        only_opposite = {(k, sign) for k, sign in first if (k, -sign) in second}
        assert only_opposite
        for _, sign in only_opposite:
            assert braid_image(2, (sign, sign)) != braid_image(2, ())
        circles += 1
        paths_checked += len(only_opposite)
    return circles, paths_checked


if __name__ == '__main__':
    for bound in (3, 4):
        circles, cuts = audit(bound)
        print(f'At most {bound} gates: {circles} two-sheet circles, {cuts} compatible full-twist cuts')
