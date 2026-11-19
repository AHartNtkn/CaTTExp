"""Check the crossing-hom pullback for a suspension in an arbitrary tensor slot."""
import argparse
import json
from collections import Counter, defaultdict
from itertools import product

from gray_globe_comparison import atom, close_atoms
from gray_tree_section import generators, tree_boundary


def verify(left, p, right):
    slot = len(left)

    def mixed_boundary(basis):
        result = Counter()
        for face, value in tree_boundary(basis).items():
            # Desuspension removes one degree to the left of all right factors.
            result[face] = -value if face[slot + 1:] != basis[slot + 1:] else value
        return result

    def atoms(space, differential):
        factors = [generators(factor) for factor in [*left, space, *right]]
        return {atom(b, differential, len) for b in product(*factors)}

    def crosses(table):
        return (table[0][0][0][slot], table[0][1][0][slot]) == (((), 0), ((), 1))

    def margin(rows, keep):
        return tuple(tuple(tuple(sorted(g[:slot] + g[slot + 1:] for g in row
                                        if keep(g[slot][0]))) for row in pair)
                     for pair in rows)

    def suspend(basis):
        address, vertex = basis[slot]
        return basis[:slot] + (((0,) + address, vertex),) + basis[slot + 1:]

    cylinder = atoms([[]], tree_boundary)
    mixed = atoms(p, mixed_boundary)
    target = atoms([p], tree_boundary)
    for degree in range(max(map(len, target))):
        by_margin = defaultdict(list)
        for v in close_atoms(mixed, degree):
            by_margin[margin(v, lambda a: not a)].append(v)
        recovered = set()
        for u in close_atoms(cylinder, degree + 1):
            if not crosses(u):
                continue
            for v in by_margin[margin(u[1:], bool)]:
                rows = [u[0]]
                for pure, inner in zip(u[1:], v):
                    pair = []
                    for face, chain in zip(pure, inner):
                        entries = [g for g in face if not g[slot][0]]
                        entries.extend(suspend(g) for g in chain)
                        pair.append(tuple(sorted(entries)))
                    rows.append(tuple(pair))
                h = tuple(rows)
                assert h not in recovered
                recovered.add(h)
        assert recovered == {h for h in close_atoms(target, degree + 1) if crosses(h)}
        print(f'Hom degree {degree}: {len(recovered)} cells')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('left', type=json.loads, help='trees before the suspended slot')
    parser.add_argument('p', type=json.loads, help='tree to suspend')
    parser.add_argument('right', type=json.loads, help='trees after the suspended slot')
    args = parser.parse_args()
    verify(args.left, args.p, args.right)
