"""Finite checks for Researcher Response 1 on invertibility in directed interchange."""

from collections import Counter, defaultdict
from itertools import product

from grid_loop_words import classes, marked_edge, swap
from interchange_pasting_minimum import face, globe, gray_layers, paste
from interchange_quotient_fibers import partitions, tensor_rows
from marked_inner_crossing import reachable, square


def check_loop():
    start, end = (2, 2), (0, 0)
    quotient = classes(start, end)
    words = [word for word in quotient if marked_edge(start, end, word, 1)]
    assert len(words) == 1
    word, = words
    assert quotient[word] == quotient[swap(word, 1)]
    # All four events are unit-area crossings. Whisker the exchange of the
    # two middle events by the events outside its window.
    areas = [1 for _ in word]
    loop = sum(areas), areas[1] * areas[2]
    identity = sum(areas), 0
    assert loop == (4, 1) and identity == (4, 0)

    def square_label(x, y):
        return x * y

    for x, y, z in product(range(-4, 5), repeat=3):
        assert square_label(x + y, z) == square_label(x, z) + square_label(y, z)
        assert square_label(x, y + z) == square_label(x, y) + square_label(x, z)
        assert square_label(x, y) + square_label(-x, y) == 0
        assert z + square_label(x, y) == square_label(x, y) + z
    print("K15 identifies the two schedules. Their exchange is (4, 1), with identity (4, 0).")


def check_strips():
    # In the directed base even an arbitrary group label cannot reverse this edge.
    rect = square((0, 0), 1, 2)
    assert rect.target in reachable(rect.source) and rect.source not in reachable(rect.target)
    tiles = partitions(2)
    grid_tags = [Counter((hi - lo, 1) for lo, hi in strip) for strip in tiles]
    assert Counter({(2, 1): 1}) in grid_tags and Counter({(1, 1): 2}) in grid_tags

    # Check the typed five-dimensional faces of the guarded W test.
    # A 5-arrow over a fixed 3-value is (source 4-label, target 4-label, tag).
    def then(f, g):
        assert f[1] == g[0]
        return f[0], g[1], f[2] + g[2]

    def disk(lo, hi, right):
        a, b = hi - lo, right[1] - right[0]
        crossing, correcting = a * b, b * a
        r = t = 0
        h = -correcting
        assert h + correcting == r
        negative, positive = t + crossing + r, h + t
        tag = int(a == 2 and b == 1)
        if not correcting:
            assert (negative, positive, tag) == (0, 0, 0)
        return negative, positive, tag

    for lo in range(3):
        for hi in range(lo, 3):
            for right in [(0, 0), (0, 1), (1, 1)]:
                s, t, z = disk(lo, hi, right)
                inverse = t, s, -z
                assert then((s, t, z), inverse) == (s, s, 0)
                assert then(inverse, (s, t, z)) == (t, t, 0)
    width_two = disk(0, 2, (0, 1))
    step = disk(0, 1, (0, 1))
    # Translate the two unit-width arrows by the unchanged other 4-face.
    pasted = then((step[0] + 1, step[1] + 1, step[2]),
                  (step[0] - 1, step[1] - 1, step[2]))
    assert width_two == (2, -2, 1) and pasted == (2, -2, 0)
    assert tensor_rows((0, 2), (0, 1))[4, 0] == (
        tensor_rows((0, 1), (0, 1))[4, 0] + tensor_rows((1, 2), (0, 1))[4, 0])
    print("Both strip evaluations separate the tiles. The outer 5-arrows have faces 2 and -2.")


def check_contraction():
    # The globe of the moving operand Z maps to the complex of a wedge of
    # three globes. The two lower slots carry the identity on the 2-cell u.
    source = globe(3, 1)
    for collapsed in (False, True):
        target = {}
        for slot, dim in enumerate((2, 2) if collapsed else (2, 2, 3)):
            def name(d, i):
                return (slot, d, i) if d else ('vertex', slot + i)
            for (d, i), row in globe(dim, 1).items():
                target[name(d, i)] = {name(*b): k for b, k in row.items()}

        def image(d, i):
            if not d:
                return Counter({('vertex', (2 if collapsed else 3) * i): 1})
            terms = [(s, d, i if d < 2 else 0) for s in (0, 1) if d <= 2]
            if not collapsed:
                terms.append((2, d, i))
            return Counter(terms)

        for generator, row in source.items():
            lhs, rhs = Counter(), Counter()
            for term, coefficient in image(*generator).items():
                lhs.update({k: coefficient * v for k, v in target[term].items()})
            for boundary, sign in row.items():
                rhs.update({k: sign * v for k, v in image(*boundary).items()})
            assert lhs == rhs
        top = Counter({(term, 'b'): v for term, v in image(3, 0).items()})
        assert top == (Counter() if collapsed else Counter({((2, 3, 0), 'b'): 1}))
    print("Both maps of the moving globe commute with the differential. Only x tensor b survives before contraction.")


def check_gray_fibres():
    total = 0
    for left_dim, right_dim in ((1, 1), (2, 1), (2, 2), (3, 1)):
        left, right = globe(left_dim, 1), globe(right_dim, 1)
        basis = list(product(left, right))
        layers = gray_layers(left, right)

        def pure_chains(cell):
            rows = [Counter(), Counter()]
            for i, (a, b) in enumerate(basis):
                if (cell[-1][0] >> i) & 1:
                    if not b[0]:
                        rows[0][a] += 1
                    if not a[0]:
                        rows[1][b] += 1
            return rows

        for d in range(1, len(layers)):
            neighbours = defaultdict(set)
            if d + 1 < len(layers):
                for edge in layers[d + 1]:
                    if not any(pure_chains(edge)):
                        s, t = face(edge, d, 0), face(edge, d, 1)
                        neighbours[s].add(t)
                        neighbours[t].add(s)
            groups = defaultdict(list)
            for cell in layers[d]:
                key = tuple(face(cell, d - 1, side) for side in (0, 1))
                chains = tuple(tuple(sorted(row.items())) for row in pure_chains(cell))
                groups[key, chains].append(cell)
            for group in groups.values():
                pending, seen = [group[0]], {group[0]}
                while pending:
                    new = neighbours[pending.pop()] - seen
                    pending.extend(new)
                    seen.update(new)
                assert seen == set(group)
                total += len(group) * (len(group) - 1)
    assert total == 48
    print(f"Mixed-cell zigzags connect all {total} distinct ordered parallel equal-image pairs on four disk tensors.")


def check_naturality():
    left, right = globe(2, 1), globe(1, 1)
    layers = gray_layers(left, right)
    basis = list(product(left, right))
    top_bit = 1 << basis.index(((2, 0), (1, 0)))

    def label(cell):
        return int(bool(cell[-1][0] & top_bit))

    assert all(label(square_face) == 0 for square_face in layers[2])
    assert {label(cell) for cell in layers[3]} == {0, 1}
    for f, g in product(layers[3], repeat=2):
        for cut in range(3):
            if face(f, cut, 1) == face(g, cut, 0):
                assert label(paste(f, g, cut)) == label(f) + label(g)
    print("The positive naturality label respects every typed composite on the (2, 1) disk.")


if __name__ == '__main__':
    check_loop()
    check_strips()
    check_contraction()
    check_gray_fibres()
    check_naturality()
