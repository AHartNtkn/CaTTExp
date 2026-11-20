"""Check compression into ordered chain factors and small strand projections."""

from collections import Counter
from itertools import combinations, permutations

from check_interchange_grid_contractions import normal_path
from check_interchange_slot_refinement import classes_on, steps
from t_endomorphisms import UF, all_extensions, expansions


def compress(start, end):
    names = sorted(start)
    level = {}
    for x in names:
        predecessors = [a for a in names if a < x and start.index(x) < start.index(a)
                        and end.index(a) < end.index(x)]
        level[x] = 1 + max((level[a] for a in predecessors), default=0)
    ordered = sorted(start, key=lambda a: (level[a], start.index(a)))
    rename = str.maketrans(dict(zip(ordered, names)))
    factors = tuple(level[a] for a in ordered)
    return rename, factors


def check_interval(start, end):
    original = classes_on(start, end)
    if not original:
        return 0, 0
    rename, factors = compress(start, end)
    paths = {word: tuple(e.translate(rename) for e in word) for word in original}
    mapped = set(paths.values())
    groups = UF()
    for path in mapped:
        for other in steps(start.translate(rename), path, factors):
            assert other in mapped
            groups.union(path, other)
    partition = {(original[p], groups.find(q)) for p, q in paths.items()}
    assert len(partition) == len(set(original.values())) == len({b for _, b in partition})

    if max(factors) <= 2:
        # The two-chain contraction reduces the whole shared equality question
        # on this interval to comparison of its two irreducible crossing words.
        rows = {chr(97+i): i for i, level in enumerate(factors) if level == 1}
        cols = {chr(97+i): i for i, level in enumerate(factors) if level == 2}
        pairs = {(original[p], normal_path(tuple((rows[a], cols[b]) for a, b in q)))
                 for p, q in paths.items()}
        assert len(pairs) == len(partition) == len({b for _, b in pairs})
    return max(factors), len(original)


def check_compression():
    counts = Counter()
    total = 0
    for n in (4, 5):
        ends = [''.join(p) for p in permutations('abcde'[:n])] if n == 4 else ['abcde']
        for p in permutations('abcde'[:n]):
            for end in ends:
                height, paths = check_interval(''.join(p), end)
                if height:
                    counts[height] += 1
                    total += paths
    assert all(counts[i] for i in range(1, 6))
    print(f"{sum(counts.values())} sorting intervals, {total} histories; "
          f"{counts[1]+counts[2]} intervals also checked by two-chain contraction.")


def restricted(word, rows, cols):
    return tuple((rows.index(i), cols.index(j)) for i, j in word if i in rows and j in cols)


def check_block(rows, cols):
    row_names = tuple(range(rows))
    col_names = tuple(range(cols))
    direct = expansions(row_names, col_names)
    # The exceptional schedules depend only on the relative row and column names.
    patterns = []
    for r, c in ((2, 3), (3, 2)):
        small_rows, small_cols = tuple(range(r)), tuple(range(c))
        bad = all_extensions(small_rows, small_cols) - expansions(small_rows, small_cols)
        assert len(bad) == 1
        patterns.extend((set((i,j) for i in rr for j in cc),
                         tuple((rr[a], cc[b]) for a, b in next(iter(bad))))
                        for rr in combinations(row_names, r)
                        for cc in combinations(col_names, c))
    histories = all_extensions(row_names, col_names)
    for word in histories:
        has_obstruction = any(tuple(e for e in word if e in events) == forbidden
                              for events, forbidden in patterns)
        assert has_obstruction == (word not in direct)
    print(f"{rows}x{cols}: five-strand test agrees with all binary subdivisions "
          f"on {len(histories)} histories, including {len(direct)} block spellings.")


def check_seven_strands():
    # Letters give row and column, with columns processed in descending order.
    def word(string):
        return tuple((int(t[0]), int(t[1])) for t in string.split())
    p = word('03 13 02 01 12 00 11 10 23 22 21 20')
    q = word('03 13 23 02 01 12 00 11 10 22 21 20')
    rows, cols = tuple(range(3)), tuple(range(4))
    assert {p, q} <= all_extensions(rows, cols)
    assert normal_path(p) != normal_path(q)
    for rr, cc in ([(r, cols) for r in combinations(rows, 2)]
                   + [(rows, c) for c in combinations(cols, 3)]):
        assert normal_path(restricted(p, rr, cc)) == normal_path(restricted(q, rr, cc))
    print("The two 3x4 histories differ, and all seven single-strand contractions agree.")


if __name__ == '__main__':
    check_compression()
    for dims in ((2, 3), (3, 3), (3, 5), (4, 4)):
        check_block(*dims)
    check_seven_strands()
