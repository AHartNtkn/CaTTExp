"""Compare stacks of all disk cylinders in P with the spanning cells of [s] ⊗ P."""
import argparse
import json
from collections import Counter, defaultdict
from functools import cache
from itertools import product

from gray_globe_comparison import atom, close_atoms, face
from gray_tree_section import generators, tree_boundary


@cache
def differential(chain):
    result = Counter()
    for g in chain:
        result.update(tree_boundary(g))
    return tuple(sorted((g, n) for g, n in result.items() if n))


def cylinder_levels(points, maximum):
    """Enumerate positive maps I ⊗ D^n → P by extending each disk boundary."""
    atoms = {atom((g,), tree_boundary, len) for g in points}
    previous = []
    for n in range(maximum + 1):
        caps = close_atoms(atoms, n)
        cap_pairs = defaultdict(list)
        for x in caps:
            cap_pairs[(face(x, 0), face(x, 1)) if n else ()].append(x)
        chains = {x[-1][0] for x in close_atoms(atoms, n + 1)}
        by_differential = defaultdict(list)
        for z in chains:
            by_differential[differential(z)].append(z)
        sides = defaultdict(list)
        for a, b, rows in previous:
            sides[(a[:-1], b[:-1], rows[:-1])].append((a, b, rows))
        if n:
            boundaries = ((cap_pairs[(a0, a1)], cap_pairs[(b0, b1)],
                           z0[:-1] + ((z0[-1][0], z1[-1][0]),))
                          for group in sides.values()
                          for (a0, b0, z0), (a1, b1, z1) in product(group, repeat=2))
        else:
            boundaries = [(caps, caps, ())]
        current = []
        for starts, ends, rows in boundaries:
            for a, b in product(starts, ends):
                # d(e ⊗ g) = (1 - 0) ⊗ g - e ⊗ dg.
                rhs = Counter(b[-1][0])
                rhs.subtract(a[-1][0])
                if rows:
                    rhs.update(rows[-1][0])
                    rhs.subtract(rows[-1][1])
                key = tuple(sorted((g, count) for g, count in rhs.items() if count))
                for z in by_differential[key]:
                    current.append((a, b, rows + ((z, z),)))
        yield current
        previous = current


def is_constant(cap):
    return all(row == ((), ()) for row in cap[1:])


def assemble(stack):
    width = len(stack) - 1
    def layer(j, chain):
        return tuple((((), j),) + g for g in chain)
    start = layer(0, stack[0][0][0][0])
    end = layer(width, stack[-1][1][0][0])
    result = [(start, end)]
    for k in range(len(stack[0][2])):
        pair = []
        for disk_side in (1, 0):  # the global mixed faces reverse disk signs
            chain = []
            for j, (a, _, rows) in enumerate(stack):
                chain.extend(layer(j, rows[k][disk_side]))
                if j:
                    chain.extend((((j - 1,), 0),) + g for g in a[k][disk_side])
            pair.append(tuple(sorted(chain)))
        result.append(tuple(pair))
    return tuple(result)


def verify(width, tree):
    if width < 1:
        raise ValueError('the spanning test needs a nonempty clock path')
    clock = generators([[] for _ in range(width)])
    points = generators(tree)
    atoms = {atom(b, tree_boundary, len) for b in product(clock, points)}
    for n, cylinders in enumerate(cylinder_levels(points, max(map(len, atoms)) - 1)):
        successors = defaultdict(list)
        for c in cylinders:
            successors[c[0]].append(c)
        def stacks(prefix):
            if len(prefix) == width + 1:
                if is_constant(prefix[-1][1]):
                    yield prefix
                return
            for nxt in successors[prefix[-1][1]]:
                yield from stacks(prefix + (nxt,))
        outputs = set()
        for c in cylinders:
            if is_constant(c[0]):
                for stack in stacks((c,)):
                    h = assemble(stack)
                    assert h not in outputs
                    outputs.add(h)
        whole = {h for h in close_atoms(atoms, n + 1)
                 if h[0][0][0][0] == ((), 0) and h[0][1][0][0] == ((), width)}
        assert whole == outputs, (n, len(whole), len(outputs))
        print(f'Global degree {n + 1}: {len(outputs)} spanning cells')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('width', type=int)
    parser.add_argument('tree', type=json.loads)
    args = parser.parse_args()
    verify(args.width, args.tree)
