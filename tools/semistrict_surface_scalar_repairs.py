"""Check strict reachability for the scalar attachment tests of Response 30."""
from collections import Counter, defaultdict, deque
from itertools import permutations, product

from gray_globe_comparison import atom, face, globe, strict_cells
from semistrict_surface_odd_cubes import EDGE


def compose(left, right, cut):
    return (left[:cut] + ((left[cut][0], right[cut][1]),)
            + tuple(tuple(tuple(sorted(a + b)) for a, b in zip(row, column))
                    for row, column in zip(left[cut+1:], right[cut+1:])))


class CubicalComparisons:
    def __init__(self, width, rank):
        self.rank = rank
        self.cells = strict_cells((1,) * width, rank - 1)
        self.starts = defaultdict(list)
        self.ends = defaultdict(list)
        for cell in self.cells:
            for cut, row in enumerate(cell[:-1]):
                self.starts[cell[:cut], row[0]].append(cell)
                self.ends[cell[:cut], row[1]].append(cell)
        self.atoms = [basis for basis in product(globe(1), repeat=width)
                      if basis.count(EDGE) == rank]

    def close_contexts(self, edges):
        """Generate all one-step moves. A breadth-first path composes them at the top cut."""
        seen = set(edges)
        pending = deque(seen)
        while pending:
            source, target = pending.popleft()
            assert source in self.cells and target in self.cells
            assert source[:-1] == target[:-1]
            for cut, row in enumerate(source[:-1]):
                for before in self.ends[source[:cut], row[0]]:
                    edge = (compose(before, source, cut), compose(before, target, cut))
                    if edge not in seen:
                        seen.add(edge)
                        pending.append(edge)
                for after in self.starts[source[:cut], row[1]]:
                    edge = (compose(source, after, cut), compose(target, after, cut))
                    if edge not in seen:
                        seen.add(edge)
                        pending.append(edge)
        return seen

    def comparisons(self, labels, repair_words):
        edges = []
        for basis in self.atoms:
            cube = atom(basis)
            source, target = face(cube, 0), face(cube, 1)
            edges.append((source, target))
            # A full reverse cube has descending temporal input order.
            word = tuple(label for slot, label in zip(basis[::-1], labels[::-1]) if slot == EDGE)
            if word in repair_words:
                edges.append((target, source))
        return self.close_contexts(edges)


def reachable(edges, start):
    successors = defaultdict(set)
    for source, target in edges:
        successors[source].add(target)
    found = {start}
    pending = [start]
    while pending:
        for target in successors[pending.pop()] - found:
            pending.append(target)
            found.add(target)
    return found


def check_facet_differences(chart):
    # Test all parallel pairs (including non-generating cell boundaries), using
    # chains obtained from closing the actual cubical atoms under every cut.
    fibres = defaultdict(list)
    for cell in chart.cells:
        fibres[cell[:-1]].append(Counter(cell[-1][0]))
    cube = atom((EDGE,) * chart.rank)
    pivot = next(iter(cube[-2][1]))
    differential = Counter(cube[-2][1])
    differential.subtract(cube[-2][0])
    different = 0
    for chains in fibres.values():
        for left, right in product(chains, repeat=2):
            delta = right.copy()
            delta.subtract(left)
            scale = delta[pivot]
            assert all(value == scale * differential[basis] for basis, value in delta.items())
            assert all(delta[basis] == scale * value for basis, value in differential.items())
            different += bool(scale)
    return different


def check_contextual_paths():
    """Recover a four-rewrite chart from its concrete descending temporal history."""
    rules = (('', ''), ('', 'f'), ('fg', ''), ('f', 'gf'))
    count = 0
    for labels in product(range(len(rules)), repeat=4):
        for middle_gap in ('', 'g', 'gg'):
            gaps = ('g', '', middle_gap, '', 'f')
            pieces = [rules[label] for label in labels]

            def word(pasts):
                chunks = [gaps[0]]
                for j, (before, after) in enumerate(pieces):
                    chunks.extend((after if j in pasts else before, gaps[j+1]))
                return ''.join(chunks)

            initial = word(set())
            final = word(set(range(4)))
            for order in permutations(range(4)):
                current = initial
                done = set()
                events = []
                for j in order:
                    before, after = pieces[j]
                    prefix = sum(len(gap) for gap in gaps[:j+1])
                    prefix += sum(len(pieces[i][i in done]) for i in range(j))
                    assert current[prefix:prefix+len(before)] == before
                    events.append((prefix, labels[j]))
                    current = current[:prefix] + after + current[prefix+len(before):]
                    done.add(j)
                    assert current == word(done)
                assert current == final
                if order == (3, 2, 1, 0):
                    start = 0
                    recovered = []
                    for pos, label in reversed(events):
                        assert start <= pos
                        recovered.extend((initial[start:pos], label))
                        start = pos + len(rules[label][0])
                    recovered.append(initial[start:])
                    expected = [item for pair in zip(gaps, labels) for item in pair] + [gaps[-1]]
                    assert recovered == expected
                count += 1
    print(f'{count:,} contextual readings with empty, contracting and expanding rewrites.')


def main():
    check_contextual_paths()
    rank = 4
    chart = CubicalComparisons(rank, rank)
    differences = check_facet_differences(chart)
    source, target = [face(atom((EDGE,) * rank), i) for i in (0, 1)]
    words = list(product('ab', repeat=rank))
    tests = 0
    for supplied in words:
        for requested in words:
            edges = chart.comparisons(requested[::-1], {supplied})
            assert (source in reachable(edges, target)) == (supplied == requested)
            tests += 1
    print(f'{tests} single-attachment tests on {len(chart.cells)} cubical 3-cells; '
          f'{differences} ordered parallel pairs with different top chains.')

    larger = CubicalComparisons(rank + 1, rank)
    labels = tuple('baaba')
    native = larger.comparisons(labels, set())
    edges = larger.comparisons(labels, {tuple('abaa')})
    added = edges - native
    assert added
    # Check composition with a genuine outside whisker: the added declaration
    # is at width four, and the boundary below uses all five occurrences.
    at_full_width = [(s, t) for s, t in added if len(s[1][0]) == rank + 1]
    assert at_full_width
    s, t = at_full_width[0]
    assert s in reachable(native, t) and t not in reachable(native, s)
    assert t in reachable(edges, s)
    print(f'{len(larger.cells)} cubical 3-cells at width five, {len(native)} contextual forward '
          f'moves and {len(at_full_width)} full-width reverse moves from the selected word.')


if __name__ == '__main__':
    main()
