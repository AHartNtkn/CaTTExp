"""Cross-check recompression and separator handling against independent expansions."""

from itertools import product
from random import Random

from interchange_shared_paths import compressed_equal, separated_equal
from interchange_comparison_fibres import strip_paths
from interchange_power_profiles import check_schedules
from marked_inner_crossing import Path, identity, square


def join(rules, a, b):
    rules.append((~a, ~b))
    return len(rules) - 1


def oracle(rules, x, y):
    # A unary gap can here be expanded into its list of named unit tiles.
    # Terminals 0 and 1 are singleton tiles; 2 abbreviates their full split.
    values = []
    for row in rules:
        values.append(tuple(j for i in row for j in (
            values[~i] if i < 0 else ((0, 1) if i == 2 else (i,)))))
    return values[x] == values[y]


def check_reassociation():
    rng = Random(341)
    checked = 0
    for _ in range(500):
        rules = [(), (0,), (1,), (2,), (3,), (4,)]
        words = [(), (0,), (1,), (2,), (3,), (4,)]
        for _ in range(25):
            a, b = rng.choices(range(len(rules)), k=2)
            join(rules, a, b)
            words.append(words[a] + words[b])
        root = len(rules) - 1
        word = words[root]
        other = 0
        for x in word:
            other = join(rules, other, 1 + x)
        for b, expanded in ((other, word), (root - 1, words[root - 1])):
            assert compressed_equal(rules, root, b) == (word == expanded)
            assert separated_equal(rules, root, b, {0, 1, 2}, oracle) == (
                oracle(rules, root, b))
            checked += 1
    print(f"{checked} compressed word and separator comparisons agree with expansion.")


def check_marked():
    # Treat complete marked-strip paths as lower labels on rigid letters.
    # Compare the actual lower evaluations in both the marked and split tables.
    for width in range(1, 7):
        paths = list(strip_paths(width))
        marked = []
        split = []
        for path in paths:
            image = identity(Path((0, 0), 'B' * width + 'A'))
            event_word = ()
            for i, j in zip(path, path[1:]):
                step = identity(Path((0, 0), 'B' * j)).horizontal(square((0, j), 1, i-j))
                image = image.vertical(step.horizontal(identity(Path((1, i), 'B' * (width-i)))))
                event_word += tuple(range(i, j, -1))
            marked.append(image.tag)
            split.append(event_word)
        # The marked table can identify cuts: it supplies sound inequalities.
        # Split refinements give an equal lower label on every path.
        assert all(word == split[0] for word in split)
        for labels in (marked, split):
            names = {v: i for i, v in enumerate(dict.fromkeys(labels))}
            rules = [(names[v],) for v in labels]
            for a, b in product(range(len(labels)), repeat=2):
                assert separated_equal(rules, a, b, set(), oracle) == (labels[a] == labels[b])
    print("Rigid-name comparison checked with marked and fully split strip evaluations through width 6.")


def check_large():
    rules = [(), (0,), (1,), (2,), (3,), (4,)]
    # (r ab s)^n and r ((ab s r)^(n-1)) ab s. Encode ab also as terminal 2.
    tail = join(rules, 3, 5)
    left = join(rules, 4, join(rules, join(rules, 1, 2), 5))
    rot = join(rules, tail, 4)
    middle = 0
    for _ in range(100):
        middle = join(rules, middle, rot)
        rot = join(rules, rot, rot)
        left = join(rules, left, left)
    right = join(rules, join(rules, 4, middle), tail)
    assert separated_equal(rules, left, right, {0, 1, 2}, oracle)
    altered = join(rules, join(rules, 4, middle), join(rules, 3, 4))
    assert not separated_equal(rules, left, altered, {0, 1, 2}, oracle)
    print("Reassociated paths with 2^100 periods compare equal; changing the final rigid label is detected.")


if __name__ == '__main__':
    check_schedules()
    check_reassociation()
    check_marked()
    check_large()
