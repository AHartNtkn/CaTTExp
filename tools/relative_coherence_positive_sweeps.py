"""Compare graph paths, ideals of generating rewrites, and all interval subdiagrams."""
from collections import Counter
from itertools import combinations


def start_string(size):
    return tuple(range(size)), tuple((i, i + 1) for i in range(size))


def replace(word, inputs, outputs):
    try:
        i = word.index(inputs[0])
    except ValueError:
        return None
    if word[i:i + len(inputs)] != inputs:
        return None
    return word[:i] + outputs + word[i + len(inputs):]


def add_face(edges, frontier, begin, consumed, produced):
    inputs = frontier[begin:begin + consumed]
    fresh = max(max(pair) for pair in edges) + 1
    vertices = (edges[inputs[0]][0], *range(fresh, fresh + produced - 1), edges[inputs[-1]][1])
    outputs = tuple(range(len(edges), len(edges) + produced))
    return edges + tuple(zip(vertices, vertices[1:])), replace(frontier, inputs, outputs), (inputs, outputs)


def paths(edges, permitted, source, target):
    outgoing = {}
    for i in permitted:
        x, y = edges[i]
        outgoing.setdefault(x, []).append((i, y))

    def visit(x, seen):
        assert x not in seen
        if x == target:
            yield ()
        else:
            for i, y in outgoing.get(x, ()):
                for rest in visit(y, seen | {x}):
                    yield (i, *rest)
    return set(visit(source, set()))


def check(start, edges, faces, counts):
    source, target = edges[start[0]][0], edges[start[-1]][1]
    graph_paths = paths(edges, range(len(edges)), source, target)
    producers = {}
    dependencies = []
    for i, (inputs, outputs) in enumerate(faces):
        dependencies.append(sum(1 << j for j in {producers[e] for e in inputs if e in producers}))
        producers.update((e, i) for e in outputs)

    states = {}
    for mask in range(1 << len(faces)):
        word = start
        for i, (inputs, outputs) in enumerate(faces):
            if mask & (1 << i):
                if dependencies[i] & ~mask:
                    break
                word = replace(word, inputs, outputs)
                assert word is not None
        else:
            states[mask] = word
    assert len(states) == len(graph_paths) and set(states.values()) == graph_paths
    for lower, word in states.items():
        # Every one-step rewrite in the whole graph is an ideal cover, and conversely.
        for i, face in enumerate(faces):
            new = replace(word, *face)
            allowed = not (lower & (1 << i) or dependencies[i] & ~lower)
            expected = states[lower | (1 << i)] if allowed else None
            assert new == expected
        for upper in states:
            if lower & ~upper:
                continue
            permitted = set(word)
            for i, (inputs, outputs) in enumerate(faces):
                if (upper ^ lower) & (1 << i):
                    permitted.update(inputs + outputs)
            cuts = {path for mid, path in states.items() if not lower & ~mid and not mid & ~upper}
            assert paths(edges, permitted, source, target) == cuts
            counts['intervals'] += 1
    counts['presentations'] += 1
    counts['paths'] += len(states)


def enumerate_small(size, depth, counts):
    start, edges = start_string(size)

    def run(edges, frontier, faces):
        check(start, edges, faces, counts)
        if len(faces) == depth:
            return
        for begin, stop in combinations(range(len(frontier) + 1), 2):
            for produced in (1, 2):
                new_edges, next_word, face = add_face(edges, frontier, begin, stop - begin, produced)
                run(new_edges, next_word, faces + (face,))
    run(edges, start, ())


if __name__ == '__main__':
    counts = Counter()
    for size in (1, 2, 3):
        enumerate_small(size, 3, counts)
    start, edges = start_string(7)
    word, faces = start, []
    for i in range(7):
        edges, word, face = add_face(edges, word, i, 1, 1)
        faces.append(face)
    check(start, edges, faces, counts)
    print(', '.join(f'{n} {name}' for name, n in counts.items()))
