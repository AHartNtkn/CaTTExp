"""Compare top-cut factorizations and simultaneous event markers with composition closure."""
from argparse import ArgumentParser
from collections import Counter
from itertools import combinations, product

from gray_globe_comparison import atom, boundary, close_atoms, globe, strict_cells
from gray_globe_section import trim


def subsets(items):
    items = tuple(items)
    for length in range(len(items) + 1):
        yield from map(frozenset, combinations(items, length))


def marker(z):
    return z + ((-1, 0),)


def check(shape):
    height = sum(shape)
    cells = {trim(c) for c in strict_cells(shape, height)}
    generators = list(product(*(globe(k) for k in shape)))
    stats = Counter()
    for n in range(1, height + 1):
        old, changes = [], {}
        for z in generators:
            t = atom(z)
            if len(t) <= n:
                old.append(t)
            elif len(t) == n + 1:
                changes[z] = tuple(map(frozenset, t[-2]))
        # Close the lower presentation with every fresh marker adjoined.
        marked_atoms = [atom(z)[:n - 1] + (((marker(z),), (marker(z),)),) for z in changes]
        marked = close_atoms(old + marked_atoms, n - 1)
        for w in (c for c in cells if len(c) == n + 1):
            stats['cells'] += 1
            events = frozenset(w[-1][0])
            start, finish = w[-2]
            predecessors = {z: {other for other in events if changes[other][1] & changes[z][0]}
                            for z in events}
            cuts = set()
            for done in subsets(events):
                remaining = events - done
                ideal = all(predecessors[z] <= done for z in done)
                state = Counter(start)
                for z in done:
                    state.update(boundary(z))
                chain = tuple(sorted(state.elements()))
                left = tuple(sorted(done))
                right = tuple(sorted(remaining))
                a = w[:-2] + ((start, chain), (left, left))
                b = w[:-2] + ((chain, finish), (right, right))
                # Identities at the top cut use their intrinsic lower tableau.
                actual = min(state.values(), default=0) >= 0 and trim(a) in cells and trim(b) in cells
                assert actual == ideal
                if not ideal:
                    continue
                assert chain not in cuts and all(v in (0, 1) for v in state.values())
                cuts.add(chain)
                stats['cuts'] += 1
                ready = [z for z in remaining if predecessors[z] <= done]
                for active in subsets(ready):
                    if not active:
                        continue
                    row = set(chain)
                    for z in active:
                        assert changes[z][0] <= row
                        row.difference_update(changes[z][0])
                        row.add(marker(z))
                    row = tuple(sorted(row))
                    assert w[:-2] + ((row, row),) in marked
                    stats['marked'] += 1
                    stats['width'] = max(stats['width'], len(active))
    print(f"{shape}: {stats['cells']} positive-dimensional cells, {stats['cuts']} ideal cuts, "
          f"{stats['marked']} nonempty marked steps, maximum simultaneous set {stats['width']}.")


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('factors', type=int, nargs='+')
    args = parser.parse_args()
    if min(args.factors) < 1:
        parser.error('use positive globe dimensions')
    check(tuple(args.factors))
