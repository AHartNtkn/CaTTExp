"""Check the r6 graded overlap recurrence against the crossing-grid path model."""

from collections import defaultdict
from itertools import product

from t_endomorphisms import UF, all_extensions, apply, blocks, expansions, words


def shortlex(path):
    return len(path), path


def successors(path, rules):
    for start in range(len(path)):
        for left, right in rules.items():
            if path[start : start + len(left)] == left:
                yield path[:start] + right + path[start + len(left) :]


def reduce_path(path, rules):
    while True:
        successor = next(successors(path, rules), None)
        if successor is None:
            return path
        path = successor


def critical_pairs(rules):
    # Inclusion ambiguities cannot occur between the reduced left sides.
    for left, other in product(rules, repeat=2):
        for overlap in range(1, min(len(left), len(other))):
            if left[-overlap:] == other[:overlap]:
                yield (left + other[overlap:], rules[left] + other[overlap:],
                       left[:-overlap] + rules[other])


def complete(weights, equations, bound):
    rules = {}
    used_overlaps = 0

    def weight(path):
        return sum(weights[edge] for edge in path)

    for degree in range(1, bound + 1):
        pairs = [(a, b) for a, b in equations if weight(a) == degree]
        for peak, a, b in critical_pairs(rules):
            if weight(peak) == degree:
                pairs.append((a, b))
                used_overlaps += reduce_path(a, rules) != reduce_path(b, rules)

        components = UF()
        for a, b in pairs:
            assert weight(a) == weight(b) == degree
            components.union(reduce_path(a, rules), reduce_path(b, rules))
        groups = defaultdict(list)
        for path in components.p:
            groups[components.find(path)].append(path)
        for group in groups.values():
            first = min(group, key=shortlex)
            rules.update((path, first) for path in group if path != first)
    return rules, used_overlaps


def grid_check(m, n, expected):
    # A letter includes its source shuffle, hence matches only at a typed site.
    weights, equations = {}, []

    def target(edge):
        source, a, b = edge
        for crossing in min(expansions(a, b)):
            source = apply(source, crossing)
        return source

    for source in words(m, n):
        for a, b in blocks(source):
            edge = (source, a, b)
            weights[edge] = len(a) * len(b)
            splits = [((a[:i], b), (a[i:], b)) for i in range(1, len(a))]
            splits += [((a, b[j:]), (a, b[:j])) for j in range(1, len(b))]
            for first, second in splits:
                first_edge = (source, *first)
                second_edge = (target(first_edge), *second)
                assert target(second_edge) == target(edge)
                equations.append(((edge,), (first_edge, second_edge)))

    rules, used = complete(weights, equations, m * n)
    assert all(reduce_path(a, rules) == reduce_path(b, rules) for a, b in equations)
    for peak, a, b in critical_pairs(rules):
        assert reduce_path(a, rules) == reduce_path(b, rules), peak

    # Independent quotient on fully expanded histories. Apply all rectangular
    # expansions in every temporal context, then compare the partitions.
    a, b = tuple(range(1, m + 1)), tuple(range(1, n + 1))
    start = tuple(('b', j) for j in b) + tuple(('a', i) for i in a)
    histories = all_extensions(a, b)
    classes = UF()
    normal_words = {}
    for path in histories:
        source = start
        letters = []
        for i, (row, col) in enumerate(path):
            for left, right in blocks(source):
                size = len(left) * len(right)
                variants = expansions(left, right)
                if path[i:i + size] in variants:
                    for variant in variants:
                        classes.union(path, path[:i] + variant + path[i + size:])
            letters.append((source, (row,), (col,)))
            source = apply(source, (row, col))
        normal_words[path] = reduce_path(tuple(letters), rules)

    partition = {(classes.find(path), normal_words[path]) for path in histories}
    assert len(partition) == len({group for group, _ in partition}) == expected
    assert len({word for _, word in partition}) == expected
    print(f"{m} x {n}: {len(histories)} histories, {expected} normal forms,"
          f" {len(rules)} rules, {used} overlaps with distinct reduced branches")
    return used


if __name__ == '__main__':
    results = [grid_check(*case) for case in [(2, 2, 1), (3, 2, 2), (2, 4, 7), (3, 3, 21)]]
    assert sum(results) > 0
