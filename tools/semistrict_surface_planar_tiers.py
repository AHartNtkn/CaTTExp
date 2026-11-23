"""Check lifted braid moves and maximal outgoing cells in marked planar tier complexes."""

from collections import Counter, defaultdict
from itertools import combinations

from tier_complex_check import build, encodings, split


def cell_end(encoding, generators, reverse):
    result = []
    pivots = []
    for tier in encoding:
        labels = [k for kind, k in tier if kind == 'v']
        if reverse:
            labels.reverse()
        pivots.extend(range(len(result), len(result) + len(labels) - 1))
        result.extend(split(tier, [{k} for k in labels], generators))
    return tuple(result), tuple(pivots)


def reduce_letters(letters):
    word = []
    for a in letters:
        if word and word[-1] == -a:
            word.pop()
        else:
            word.append(a)
    return tuple(word)


def artin_step(images, i):
    """Artin action of one positive generator on the free group basis."""
    a, b = images[i:i + 2]
    conjugate = reduce_letters((*a, *b, *(-k for k in reversed(a))))
    return (*images[:i], conjugate, a, *images[i + 2:])


def check(size, steps, counts):
    source, target, generators = build(size, steps)
    cells = {}
    for cell in encodings(source, target, generators):
        first, pivots = cell_end(cell, generators, True)
        last, _ = cell_end(cell, generators, False)
        assert (first, pivots) not in cells
        cells[first, pivots] = last
        counts['tier cells'] += 1

    states = [v for v, cuts in cells if not cuts]
    moves = range(len(steps) - 1)

    def follow(v, word):
        for i in word:
            v = cells.get((v, (i,)))
            if v is None:
                break
        return v

    for v in states:
        for i, j in combinations(moves, 2):
            a, b = ((i, j, i), (j, i, j)) if i + 1 == j else ((i, j), (j, i))
            end = follow(v, a)
            assert end == follow(v, b)
            if (v, (i,)) in cells and (v, (j,)) in cells:
                assert end is not None and cells[v, (i, j)] == end
                counts['coinitial braid or commutation cells'] += 1
            counts['two-sided lift tests'] += 1

    # Work in the braid-labelled lift, keeping different positive loops
    # even if their projected temporal lists agree. For every reached top
    # check all vertices below it against the actual permutohedral cells.
    initials = sorted(states, key=lambda v: -sum((v, (i,)) in cells for i in moves))[:2]
    for start in initials:
        unit = tuple((i + 1,) for i in range(len(steps)))
        level = {unit}
        states_at = {unit: start}
        parents = defaultdict(set)
        children = defaultdict(dict)
        for _ in range(6):
            later = set()
            for braid in level:
                v = states_at[braid]
                for i in moves:
                    end = cells.get((v, (i,)))
                    if end is None:
                        continue
                    other = artin_step(braid, i)
                    assert states_at.setdefault(other, end) == end
                    parents[other].add(braid)
                    children[braid][i] = other
                    later.add(other)
            level = later
        for top in states_at:
            interval = {top}
            stack = [top]
            while stack:
                for prev in parents[stack.pop()] - interval:
                    interval.add(prev)
                    stack.append(prev)
            assert unit in interval
            for braid in interval:
                pivots = tuple(i for i, w in sorted(children[braid].items()) if w in interval)
                expected = cells[states_at[braid], pivots]
                # Reverse each consecutive run by adjacent transpositions.
                sink = braid
                for i in pivots:
                    j = i
                    while True:
                        sink = children[sink][j]
                        if j - 1 not in pivots:
                            break
                        j -= 1
                assert sink in interval and states_at[sink] == expected
                counts['maximal cells in lifted intervals'] += 1


if __name__ == '__main__':
    counts = Counter()
    for size, steps in [
        (0, [(0, 0, 0)] * 4),
        (0, [(0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 0)]),
        (0, [(0, 2, 0), (0, 0, 1), (2, 0, 0), (0, 0, 0)]),
        (2, [(1, 2, 0), (0, 1, 2), (1, 0, 2), (2, 1, 0)]),
        (1, [(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1)]),
    ]:
        check(size, steps, counts)
    for label, n in sorted(counts.items()):
        print(f'{n:,} {label}')
