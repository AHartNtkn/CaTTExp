"""Evaluate the determinant digits on a weighted crossing grid against K52."""

from collections import defaultdict
from fractions import Fraction
from itertools import combinations

from interchange_normal_form_check import complete, reduce_path, shortlex
from t_endomorphisms import apply, blocks, expansions, words


def determinant(matrix):
    rows = [list(map(Fraction, row)) for row in matrix]
    det = 1
    for i in range(len(rows)):
        pivot = next((j for j in range(i, len(rows)) if rows[j][i]), None)
        if pivot is None:
            return 0
        if pivot != i:
            rows[i], rows[pivot] = rows[pivot], rows[i]
            det = -det
        factor = rows[i][i]
        det *= factor
        for j in range(i + 1, len(rows)):
            ratio = rows[j][i] / factor
            for k in range(i + 1, len(rows)):
                rows[j][k] -= ratio * rows[i][k]
    return det


def least_exponent(laplacian):
    # Compute the first nonzero coefficient directly by principal minors.
    n = len(laplacian)
    for exponent in range(1, 1 << n):
        keep = [i for i in range(n) if not exponent & (1 << i)]
        if determinant([[laplacian[i][j] for j in keep] for i in keep]):
            return exponent
    raise AssertionError("the leading diagonal monomial is present")


def check():
    weights = {}
    equations = []
    outgoing = defaultdict(list)
    for source in words(2, 2):
        for left, right in blocks(source):
            edge = (source, left, right)
            target = source
            for crossing in min(expansions(left, right)):
                target = apply(target, crossing)
            outgoing[source].append((edge, target))
            weights[edge] = len(left) * len(right)
    for edge in weights:
        source, left, right = edge
        splits = [((left[:i], right), (left[i:], right)) for i in range(1, len(left))]
        splits += [((left, right[j:]), (left, right[:j])) for j in range(1, len(right))]
        for first, second in splits:
            mid = next(t for e, t in outgoing[source] if e == (source, *first))
            equations.append(((edge,), ((source, *first), (mid, *second))))
    rules, _ = complete(weights, equations, 4)
    layers = defaultdict(list)

    def extend(start, current, path, weight):
        layers[start, current, weight].append(path)
        for e, t in outgoing[current]:
            extend(start, t, path + (e,), weight + weights[e])

    for source in words(2, 2):
        extend(source, source, (), 0)
    normal = {()}
    total = 0
    for paths in layers.values():
        paths.sort(key=shortlex)
        n = len(paths)
        laplacian = [[0]*n for _ in paths]
        for i, j in combinations(range(n), 2):
            x, y = paths[i], paths[j]
            if any(x[:k]+r+x[k+len(l):] == y
                   for pair in equations for l, r in (pair, pair[::-1])
                   for k in range(len(x)) if x[k:k+len(l)] == l):
                laplacian[i][i] += 1
                laplacian[j][j] += 1
                laplacian[i][j] -= 1
                laplacian[j][i] -= 1
        digits = least_exponent(laplacian)
        for i, word in enumerate(paths):
            assert bool(digits & (1 << i)) == (reduce_path(word, rules) == word)
            if digits & (1 << i):
                normal.add(word)
        total += n
    forbidden = {w for paths in layers.values() for w in paths
                 if w not in normal and w[1:] in normal and w[:-1] in normal}
    assert forbidden == set(rules)
    print(f"{total} typed paths in {len(layers)} layers; every determinant digit and all {len(rules)} forbidden factors agree.")


if __name__ == "__main__":
    check()
