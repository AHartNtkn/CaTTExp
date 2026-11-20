"""Choose two strict five-front sweeps and compute their sufficient RC(4) slice tests."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from graphlib import TopologicalSorter
from itertools import combinations

from relative_coherence_oriental_wedges import simplex_atom, simplex_d, support
from relative_coherence_tree_folds import weak_three_skeleton


POINTS = (
    (0, 0, 0, -65, -82, 17),
    (213, -171, 82, 21, -13, -36),
    (283, -495, 31, -83, -17, -68),
    (300, 1300, 700, 53, -91, -44),
    (472, -610, 119, -75, -26, -15),
    (500, -1100, 0, -75, 88, 4),
    (700, 100, 100, 73, 30, -44),
)


class FlagSimplex:
    def __init__(self, points):
        self.vertices = tuple(range(len(points)))
        self.d, self.det = {}, {}
        for size in range(1, len(points)+1):
            for s in combinations(self.vertices, size):
                if size == 1:
                    self.det[s], self.d[s] = 1, {}
                    continue
                deletion = simplex_d(s)
                # Expand det[1, x1, ..., x_{size-1}] along its last column.
                value = (-1)**(size-1) * sum(
                    (-1)**j * points[v][size-2] * self.det[s[:j]+s[j+1:]]
                    for j,v in enumerate(s))
                assert value != 0
                self.det[s] = value
                self.d[s] = {f: sign * (1 if value*self.det[f] > 0 else -1)
                             for f,sign in deletion.items()}

    def atom(self, s):
        return simplex_atom(s, self.d.__getitem__)

    def check(self):
        orders = [TopologicalSorter() for _ in range(len(self.vertices)-1)]
        sources = [defaultdict(set) for _ in orders]
        targets = [defaultdict(set) for _ in orders]
        for s in self.d:
            rows = self.atom(s)
            assert all(len(side) == 1 for side in rows[0])
            if len(s) in (3,4):
                assert all(rows[-2])
                assert set(rows[1][0]).isdisjoint(rows[1][1])
            for j,(a,b) in enumerate(rows[:-1]):
                for f in a:
                    sources[j][f].add(s)
                for f in b:
                    targets[j][f].add(s)
        for j, order in enumerate(orders):
            for f, later in sources[j].items():
                for s in later:
                    order.add(s, *targets[j][f])
            tuple(order.static_order())

    def sweep(self, row, start, end):
        """Each entry retains the whole front before and after the atomic step."""
        current = frozenset(start)
        remaining = set(row)
        assert len(remaining) == len(row)
        steps = []
        while remaining:
            for atom in sorted(remaining):
                before, after = map(frozenset, self.atom(atom)[-2])
                if before <= current and not after & current:
                    following = (current-before) | after
                    steps.append((current, atom, following))
                    current = following
                    remaining.remove(atom)
                    break
            else:
                raise ValueError('no atomic five-step at this front')
        assert current == frozenset(end)
        return steps

    def all_slices(self, upper, lower):
        """A nonnegative join row gives both cut-three factors in the tableau category."""
        assert len(upper) == len(set(upper))
        initial, final = map(Counter, lower)
        def change(prefix):
            counts = Counter()
            for atom in prefix:
                counts.update(self.d[atom])
            return counts

        states = set()
        for k in range(len(upper)+1):
            for prefix in combinations(sorted(upper), k):
                middle = initial.copy()
                middle.update(change(prefix))
                if any(n < 0 for n in middle.values()):
                    continue
                endpoint = middle.copy()
                endpoint.update(change(upper - set(prefix)))
                assert endpoint == final
                states.add(tuple(sorted(middle.elements())))
        return states


def verify(show=False):
    flag = FlagSimplex(POINTS)
    flag.check()
    top = flag.atom(flag.vertices)
    sweeps = [flag.sweep(side, *top[4]) for side in top[5]]
    fronts = {front for path in sweeps for a,_,b in path for front in (a,b)}
    cells = {top[:3] + ((s,s),) for front in fronts for s in flag.all_slices(front, top[3])}
    full = {q for q in cells if len({i for s in support(q) for i in s}) == 7}
    weights = Counter(len(q[3][0]) for q in full)
    assert len(fronts) == 7 and weights == {10: 3, 11: 6, 12: 3}
    degree = 1 if flag.det[flag.vertices] > 0 else -1
    print(f'127 unital atoms, six acyclic cut orders, signed degree {degree:+d}.')
    for path in sweeps:
        print('Five-facet sweep, by omitted name:',
              *[next(iter(set(flag.vertices)-set(s))) for _,s,_ in path])
    print(f'{len(fronts)} four-fronts, {len(cells)} three-slices, {len(full)} full labels: {dict(sorted(weights.items()))}')
    if show:
        for i,q in enumerate(sorted(full),1):
            print(f'Slice {i}: {q}')
    weak_three_skeleton(flag)
    return full


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--slices', action='store_true', help='print all full slice tableaux')
    verify(parser.parse_args().slices)
