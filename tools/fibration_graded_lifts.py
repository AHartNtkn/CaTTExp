"""Check the height of base occurrences on strict lifts from a cyclic graph fibre."""

import argparse
from collections import Counter, defaultdict
from itertools import combinations, product

from fibration_factor_search import Rule, Stage
from gray_globe_comparison import atom, close_atoms, face, globe


def interval_boundary(basis):
    (j, p), (k, q) = basis
    differential = Counter()
    if j:
        differential[((0, p), (k, q))] -= 1
        differential[((0, p + 1), (k, q))] += 1
    if k:
        sign = (-1) ** j
        differential[((j, p), (k - 1, 0))] -= sign
        differential[((j, p), (k - 1, 1))] += sign
    return differential


def moment(side):
    return sum(p for (j, p), _ in side[-1][0] if j == 0)


def check(width, base_degree):
    # Unwrap the one-object fibre loop between heights zero and width.
    interval = [(0, p) for p in range(width + 1)] + [(1, p) for p in range(width)]
    atoms = [atom(basis, interval_boundary) for basis in product(interval, globe(base_degree))]
    total = moving = longest = 0
    for d in range(2, base_degree + 2):
        cells = close_atoms(atoms, d)
        found = False
        for c in cells:
            start, end = (pole[0][0][1] for pole in c[0])
            if start != 0 or end != width:
                continue
            total += 1
            labels = c[-1][0]
            if not labels or any(j == 0 for (j, p), q in labels):
                continue
            # Every nonidentity top atom moves one object occurrence one height unit.
            assert moment(face(c, 1)) - moment(face(c, 0)) == len(labels)
            found = True
            moving += 1
            longest = max(longest, len(labels))
        assert found, d
    assert longest == width
    print(f'Width {width}, base D{base_degree}: {total} cells at the selected heights, '
          f'{moving} positive moment changes, largest change {longest}.')


def check_signed_pentagon():
    stage = Stage({letter: ('x', 'x') for letter in 'gt'},
                  {'u': Rule('x', 'gtt', 't'), 'c': Rule('x', 'gt', 'tg')})

    def grade(word):
        return word.count('g') - word.count('t')

    assert all(grade(r.source) == grade(r.target) for r in stage.rules.values())
    # Every word of grade -1 projecting to t^4 has three g's.
    words = {''.join('g' if i in pos else 't' for i in range(7))
             for pos in combinations(range(7), 3)}
    sources = defaultdict(list)
    for w, path in stage.ending_at('x', 't', {'u'}, 3):
        assert w in words
        sources[w].append(path)
    prism = {'M': ('x', 'ggtt', (('u', 1), ('c', 0)), (('c', 1), ('c', 2), ('u', 0)))}

    def position_sum(w, path):
        return sum(grade(v[i + len(stage.rules[g].source):])
                   for v, (g, i) in zip(stage.slices('x', w, path), path) if g == 'u')

    count = moves = 0
    for w, paths in sources.items():
        cells, index = stage.quotient(paths)
        heights = []
        for reps in cells:
            values = {position_sum(w, p) for p in reps}
            assert len(values) == 1
            heights.append(values.pop())
        edges = stage.edges('x', w, cells, index, prism)
        assert all(heights[b] - heights[a] == 1 for a, _, b in edges)
        count += len(cells)
        moves += len(edges)
    assert len(words) == 35 and len(sources) == 5 and moves > 0
    print(f'Signed pentagon: {len(words)} input words at grade -1, {len(sources)} reach the pole, '
          f'{count} middle cells and {moves} checked naturality moves.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('width', type=int, nargs='?', default=3)
    parser.add_argument('base_degree', type=int, nargs='?', default=5)
    args = parser.parse_args()
    if min(args.width, args.base_degree) < 1:
        parser.error('width and base degree must be positive')
    check_signed_pentagon()
    check(args.width, args.base_degree)
