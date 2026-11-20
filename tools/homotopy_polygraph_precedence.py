"""Check the one-resource witness calculation and its strict factors on semaphore rings."""

from collections import Counter
from functools import cache
from itertools import combinations, permutations, product

from homotopy_polygraph_semaphore import Ring, clock_chart, typed_presentation


def masks(bits):
    part = bits
    while part:
        yield part
        part = (part - 1) & bits


def betti(faces):
    """Ranks over F_2 for a downwards-closed set of nonempty bit masks."""
    counts, ranks = Counter(), Counter()
    pivots = {}
    ids = {f: i for i, f in enumerate(sorted(faces))}
    for f in faces:
        dim = f.bit_count() - 1
        counts[dim] += 1
        column = 0
        bits = f
        while bits and dim:
            bit = bits & -bits
            column ^= 1 << ids[f ^ bit]
            bits ^= bit
        while column and column.bit_length() in pivots:
            column ^= pivots[column.bit_length()]
        if column:
            pivots[column.bit_length()] = column
            ranks[dim] += 1
    result = [counts[d] - ranks[d] - ranks[d + 1] for d in range(max(counts, default=-1) + 1)]
    while result and not result[-1]:
        result.pop()
    return tuple(result)


def check_ring(rows, cols, missing, *, disabled=(), edges_only=False):
    """Enumerate charts for all positions, then compute the actual precedence-cover nerve."""
    programs = [[] for _ in range(rows)] + [[('P', 0)] for _ in range(cols)]
    n = len(programs)
    initial = [Counter({0: 1}) if i < rows else Counter() for i in range(n)]
    for r, (a, b) in enumerate(missing, 1):
        for i in range(n):
            if i != a:
                initial[i][r] = 1
        if (a, b) in disabled:
            spectator = next(i for i in range(n) if i not in (a, rows + b))
            initial[spectator][r] = 0
        programs[a].append(('P', r))
        programs[rows + b].append(('V', r))
    for a in range(rows):
        programs[a].append(('V', 0))

    layout = Ring(n)
    declarations = len(typed_presentation(layout, programs))
    end = tuple(map(len, programs))
    states = []
    for program, counts in zip(programs, initial):
        state = counts.copy()
        row = [state.copy()]
        for kind, resource in program:
            state[resource] += 1 if kind == 'P' else -1
            assert state[resource] >= 0
            row.append(state.copy())
        states.append(row)

    edges = {}
    legal = Counter()
    for pos in product(*(range(t + 1) for t in end)):
        axes = [i for i, t in enumerate(pos) if t < end[i]]
        edges[pos] = []
        for size in range(min(len(axes), 1) + 1 if edges_only else len(axes) + 1):
            for moving in combinations(axes, size):
                # The maximum holding on each coordinate is attained at a corner.
                capacity = all(any(max(states[i][t][r], states[i][t + (i in moving)][r]) == 0
                                   for i, t in enumerate(pos)) for r in range(len(missing) + 1))
                actual = clock_chart(layout, programs, states, pos, moving, len(missing) + 1)
                assert actual == capacity, (pos, moving)
                if actual:
                    legal[size] += 1
                    if size == 1:
                        edges[pos].append(moving[0])

    def nerve_for(start, stop, release_rows, acquire_cols):
        pairs = list(product(release_rows, acquire_cols))
        faces = set()

        @cache
        def feasible(extra, pos):
            if pos == stop:
                return True
            for i in edges[pos]:
                if pos[i] == stop[i]:
                    continue
                if i >= rows and pos[i] == 0:
                    if any(b == i - rows and pos[a] < end[a] and extra & (1 << j)
                           for j, (a, b) in enumerate(pairs)):
                        continue
                nxt = list(pos)
                nxt[i] += 1
                if feasible(extra, tuple(nxt)):
                    return True
            return False

        for mask in range(1, 1 << len(pairs)):
            if feasible(mask, start):
                faces.add(mask)
        feasible.cache_clear()
        return betti(faces)

    zero = (0,) * n
    full = nerve_for(zero, end, range(rows), range(cols))
    sample = 'vertices and edges' if edges_only else 'cubes'
    print(f'{rows} by {cols}: {declarations} declarations, {sum(legal.values())} legal {sample}, '
          f'full witness nerve Betti numbers {full}.')
    if rows == 4:
        # Keep the apex release for the final suffix. The six other threads finish.
        stop = list(end)
        stop[3] = 0
        middle = nerve_for(zero, tuple(stop), range(3), range(cols))
        assert middle == (1, 1) and 3 in edges[tuple(stop)]
        print('Before the apex release: proper strict factor with Betti numbers', middle)
    return full


def matrix_audit():
    rows = cols = 3
    all_pairs = (1 << (rows * cols)) - 1
    bad = set()
    for allowed in range(all_pairs + 1):
        faces = set()
        for j in range(cols):
            column = sum(1 << i for i in range(rows) if allowed & (1 << (i * cols + j)))
            faces.update(masks(column))
        if any(betti(faces)[1:]):
            bad.add(allowed)

    # Vary every optional precedence and both participating vertex subsets.
    for required in range(all_pairs + 1):
        predicted = any(all(not required & (1 << (i * cols + j)) for i, j in enumerate(p))
                        for p in permutations(range(cols)))
        found = False
        for a in masks(7):
            for b in masks(7):
                selected = sum(1 << (i * cols + j) for i in range(rows) for j in range(cols)
                               if a & (1 << i) and b & (1 << j))
                forced = required & selected
                found |= any(table & ~selected == 0 and table & forced == forced for table in bad)
        assert found == predicted, required
    print('All 512 three-by-three inputs agree with the matching criterion; '
          f'{len(bad)} complete endpoint tables have positive first Betti number.')


if __name__ == '__main__':
    diagonal = [(0, 0), (1, 1), (2, 2)]
    assert check_ring(3, 3, diagonal) == (1, 1)
    assert check_ring(4, 3, diagonal) == (1,)
    assert check_ring(3, 3, diagonal + [(0, 1)], disabled={(0, 1)}, edges_only=True) == (1, 1)
    matrix_audit()
