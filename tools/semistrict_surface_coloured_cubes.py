"""Check the occurrence lift and the even- and odd-rank scalar cube obstruction."""
from collections import Counter
from itertools import combinations, permutations

from gray_globe_comparison import atom, boundary
from semistrict_surface_odd_cubes import EDGE


def schedule(rank, hemisphere, last_first):
    """Read one actual 2-face tableau as a sequence of adjacent swaps."""
    path = list(reversed(range(rank)))
    pending = set(hemisphere)
    moves = []
    while pending:
        available = []
        for i, (right, left) in enumerate(zip(path, path[1:])):
            if right < left:
                continue
            square = tuple(EDGE if j in (right, left) else (0, int(j in path[:i]))
                           for j in range(rank))
            if square in pending:
                available.append((i, square))
        assert available, (path, pending)
        i, square = available[-1 if last_first else 0]
        pending.remove(square)
        moves.append(i)
        path[i], path[i + 1] = path[i + 1], path[i]
    assert path == list(range(rank))
    return tuple(moves)


def read_colours(path, moves):
    path = list(path)
    pairs = Counter()
    for i in moves:
        right, left = path[i:i + 2]
        pairs[left, right] += 1
        path[i], path[i + 1] = left, right
    return tuple(path), pairs


def check_four_cube():
    """Reconstruct both folded 3-faces as routes of braid moves on four letters."""
    initial = (3, 2, 1, 0)
    words = set()

    def descend(path, word):
        if path == initial[::-1]:
            words.add(word)
        for i in range(3):
            if path[i] > path[i + 1]:
                new_path, _ = read_colours(path, (i,))
                descend(new_path, word + (i,))

    descend(initial, ())
    # Exchange of two disjoint square steps is strict in the fixed hom.
    classes = {}
    for word in words:
        if word in classes:
            continue
        seen = {word}
        pending = [word]
        while pending:
            w = pending.pop()
            for i, (a, b) in enumerate(zip(w, w[1:])):
                swapped = w[:i] + (b, a) + w[i+2:]
                if abs(a - b) > 1 and swapped not in seen:
                    assert swapped in words
                    seen.add(swapped)
                    pending.append(swapped)
        classes.update(dict.fromkeys(seen, min(seen)))
    edges = {c: set() for c in classes.values()}
    for w in words:
        for j in range(len(w) - 2):
            a, b, c = w[j:j+3]
            if a != c or b != a + 1:
                continue
            target = w[:j] + (b, a, b) + w[j+3:]
            path, _ = read_colours(initial, w[:j])
            active = path[a:a+3]
            face = tuple(EDGE if i in active else (0, int(i in path[:a])) for i in range(4))
            edges[classes[w]].add((classes[target], face))

    rows = atom((EDGE,) * 4)
    start, finish = (classes[schedule(4, side, False)] for side in rows[2])
    routes = []

    def walk(current, route):
        if current == finish:
            routes.append(tuple(sorted(route)))
        for successor, face in edges[current]:
            # A forward braid replacement increases the sum of letter indices.
            assert sum(successor) > sum(current)
            walk(successor, route + (face,))

    walk(start, ())
    assert len(words) == 16 and len(edges) == 8
    assert sorted(routes) == sorted(rows[3])
    print('Recovered both four-step facet routes on all 16 reduced four-letter readings.')


def check():
    check_four_cube()
    counts = Counter()
    for rank in range(2, 9):
        cube = (EDGE,) * rank
        rows = atom(cube)
        # Each bit is completed once. Sorting edges by number of completed bits
        # reads the vertex-to-vertex path even when the tableau stores a chain.
        paths = [tuple(edge.index(EDGE) for edge in sorted(side, key=lambda b: b.count((0, 1))))
                 for side in rows[1]]
        assert paths == [tuple(reversed(range(rank))), tuple(range(rank))]
        schedules = {schedule(rank, side, last_first) for side in rows[2]
                     for last_first in (False, True)}

        for axes in permutations(range(rank)):
            expected = Counter(combinations(axes, 2))
            for moves in schedules:
                final, pairs = read_colours(axes[::-1], moves)
                assert final == axes and pairs == expected
                assert all(x < y for x, y in pairs) == (axes == paths[1])
                counts['coloured hemisphere readings'] += 1

        if rank >= 3:
            # The (rank-1)-facets retain both their ordered list and base set.
            def face_key(face):
                return (tuple(j for j in range(rank) if face[j] == EDGE),
                        tuple(j for j in range(rank) if face[j] == (0, 1)))

            source, target = [Counter(map(face_key, side)) for side in rows[-2]]
            diff = target.copy()
            diff.subtract(source)
            assert diff == Counter({face_key(face): coeff for face, coeff in boundary(cube).items()})
            key = (tuple(range(1, rank)), (0,))
            assert diff[key] == 1 and source[key] - target[key] == -1
            counts['signed forward and reverse boundary pairs'] += 1

    # A braid relation inside a longer word and an exchange of disjoint swaps
    # retain the ordered-pair counts, even for nonmonotone colour assignments.
    for path in permutations(range(6)):
        for i in range(4):
            assert read_colours(path, [i, i+1, i]) == read_colours(path, [i+1, i, i+1])
            counts['whiskered braid relations'] += 1
        for i, j in combinations(range(5), 2):
            if j > i + 1:
                assert read_colours(path, [i, j]) == read_colours(path, [j, i])
                counts['disjoint exchanges'] += 1
    for label, value in counts.items():
        print(f'{value:,} {label}')


if __name__ == '__main__':
    check()
