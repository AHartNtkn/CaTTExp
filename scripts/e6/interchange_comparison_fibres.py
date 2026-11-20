"""Check the r9 fibre rank formula on outer grids and the cut test on inner strips."""

from collections import defaultdict
from fractions import Fraction

from interchange_normal_form_check import complete, reduce_path, shortlex
from marked_inner_crossing import Path, identity, square
from t_endomorphisms import apply, blocks, expansions, words


def add_column(basis, column):
    """Insert a sparse rational column into an echelon basis. Report a rank gain."""
    column = dict(column)
    while column:
        pivot = min(column)
        factor = column[pivot]
        if pivot not in basis:
            basis[pivot] = {i: Fraction(x, factor) for i, x in column.items()}
            return True
        for i, x in basis[pivot].items():
            value = column.get(i, 0) - factor * x
            if value:
                column[i] = value
            else:
                column.pop(i, None)
    return False


def check_outer_grid(m, n):
    # In global degree three both theories have both outer subdivisions.
    outgoing = defaultdict(list)
    weights, targets, splits = {}, {}, defaultdict(list)
    for state in words(m, n):
        for a, b in blocks(state):
            edge = state, a, b
            outgoing[state].append(edge)
            weights[edge] = len(a) * len(b)
            end = state
            for pair in min(expansions(a, b)):
                end = apply(end, pair)
            targets[edge] = end
    equations = []
    for edge in weights:
        state, a, b = edge
        cuts = [((a[:i], b), (a[i:], b)) for i in range(1, len(a))]
        cuts += [((a, b[i:]), (a, b[:i])) for i in range(1, len(b))]
        for left, right in cuts:
            first = (state, *left)
            expansion = first, (targets[first], *right)
            splits[edge].append(expansion)
            equations.append(((edge,), expansion))

    layers = defaultdict(list)

    def extend(start, end, path):
        layers[start, end].append(path)
        for edge in outgoing[end]:
            extend(start, targets[edge], path + (edge,))

    for start in words(m, n):
        extend(start, start, ())
    rules, _ = complete(weights, equations, m * n)
    raw = classes = 0
    for paths in layers.values():
        paths.sort(key=shortlex)
        indices = {path: i for i, path in enumerate(paths)}
        basis = {}
        for i, path in enumerate(paths):
            for k, edge in enumerate(path):
                for pair in splits[edge]:
                    j = indices[path[:k] + pair + path[k + 1:]]
                    add_column(basis, {i: 1, j: -1})
        nullity = len(paths) - len(basis)
        augmented = basis.copy()
        selected = [p for i, p in enumerate(paths) if add_column(augmented, {i: 1})]
        assert len(selected) == nullity
        assert selected == [p for p in paths if reduce_path(p, rules) == p]
        for j, path in enumerate(paths):
            lifts = []
            for normal in selected:
                i = indices[normal]
                difference = {} if i == j else {i: 1, j: -1}
                if not add_column(basis.copy(), difference):
                    lifts.append(normal)
            assert lifts == [reduce_path(path, rules)]
        raw += len(paths)
        classes += nullity
    return raw, classes


def strip_paths(i):
    if i == 0:
        yield (0,)
    for j in range(i):
        for tail in strip_paths(j):
            yield (i,) + tail


def two_advance_image(path, k):
    # Retain precisely B_k and B_(k+1). All other advances become identities.
    retained = [min(2, max(0, i - k + 1)) for i in path]
    value = identity(Path((0, 0), "BBA"))
    for i, j in zip(retained, retained[1:]):
        prefix = identity(Path((0, 0), "B" * j))
        block = square((0, j), 1, i - j)
        suffix = identity(Path((1, i), "B" * (2 - i)))
        value = value.vertical(prefix.horizontal(block).horizontal(suffix))
    assert value.target == Path((0, 0), "ABB")
    return value.tag


def check_strip(m):
    profiles = set()
    for path in strip_paths(m):
        signature = tuple(two_advance_image(path, k) for k in range(1, m))
        for k, tag in enumerate(signature, 1):
            assert tag == ({(1, 1)} if k in path else {(1, 2)})
        assert signature not in profiles
        profiles.add(signature)
        # Expand each jump in T, recording the actual advances crossed.
        expanded = [b for i, j in zip(path, path[1:]) for b in range(i, j, -1)]
        assert expanded == list(range(m, 0, -1))
    assert len(profiles) == 2 ** (m - 1)
    return len(profiles)


if __name__ == "__main__":
    for size in [(2, 2), (3, 2)]:
        raw, classes = check_outer_grid(*size)
        print(f"Outer {size}: {raw} paths, {classes} rank-selected normal forms")
    print("Inner strip fibre sizes m=1..9:", [check_strip(m) for m in range(1, 10)])
