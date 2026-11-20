"""Fold the faces of a cube onto the faces of a simplex by binary decisions."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from graphlib import TopologicalSorter
from itertools import combinations, product

from catt import check_ctx, comp2, src, tgt, v
from rc2 import kappa
from relative_coherence_based_columns import Brackets, difference
from relative_coherence_cube_boundary import boundary
from relative_coherence_oriental_wedges import simplex_d, support
from relative_coherence_state_colours import inventory
from relative_coherence_steiner_cuts import tableau


class TreeFold:
    """At (axis, left, right), the bit equal to the seed follows the left branch."""
    def __init__(self, tree, seed):
        self.tree = tree
        self.seed = seed
        self.d = {}
        self.sign = {}

    @cache
    def carrier(self, face):
        def visit(node):
            if isinstance(node, int):
                return (node,)
            i, left, right = node
            if face[i] == 0:
                return visit(left) + visit(right)
            off_seed = (face[i] == 1) != bool(self.seed & (1 << i))
            return visit(right if off_seed else left)
        return tuple(sorted(visit(self.tree)))

    def basis(self, face):
        simplex = self.carrier(face)
        return (simplex,) if len(simplex) == face.count(0)+1 else ()

    def rows(self, rows):
        return tuple(tuple(tuple(sorted(s for f in chain for s in self.basis(f)))
                           for chain in pair) for pair in rows)

    @cache
    def atom(self, simplex):
        sides = []
        for sign in (-1, 1):
            chain = Counter({simplex: 1})
            rows = []
            for _ in simplex:
                rows.append(tuple(sorted(chain.elements())))
                change = Counter()
                for s, n in chain.items():
                    for f, a in self.d[s].items():
                        change[f] += sign*n*a
                chain = +change
            sides.append(rows[::-1])
        return tuple(zip(*sides))

    def check(self, n):
        faces = list(product((-1, 0, 1), repeat=n))
        for f in faces:
            image = self.basis(f)
            change = Counter()
            for g, a in boundary(f):
                for s in self.basis(g):
                    change[s] += a
            change = {s: a for s,a in change.items() if a}
            if image:
                s, = image
                assert self.d.setdefault(s, change) == change
            else:
                assert not change
        simplices = [s for k in range(1,n+2) for s in combinations(range(n+1), k)]
        assert set(self.d) == set(simplices)
        order = TopologicalSorter()
        for s in simplices:
            if len(s) == 1:
                self.sign[s] = 1
                continue
            deletion = simplex_d(s)
            assert self.d[s].keys() == deletion.keys()
            signs = {a * self.sign[f] * deletion[f] for f,a in self.d[s].items()}
            sign, = signs
            assert sign in (-1, 1)
            self.sign[s] = sign
            for f,a in self.d[s].items():
                if a > 0:
                    order.add(f, s)
                else:
                    order.add(s, f)
        assert len(tuple(order.static_order())) == len(simplices)
        for f in faces:
            s = self.carrier(f)
            expected = self.atom(s) + (((), ()),) * (f.count(0)+1-len(s))
            assert self.rows(tableau(f)) == expected
            assert all(len(chain) == 1 for chain in expected[0])
        return self.sign[tuple(range(n+1))]


def six_fold():
    # The first axis met off seed in this decision tree determines the leaf.
    tree = (5, (4, (3, (2, (1, (0, 0, 1), 2), 3), 4), 5), 6)
    return TreeFold(tree, 16)


def check_states(fold, show=False):
    states, carriers, _ = inventory()
    lower = tableau((0,)*6)[:3]
    all_names = set(range(7))
    full = Counter()
    all_images = set()
    for state, (vertices, _) in zip(states, carriers):
        row = tuple(sorted(state))
        q = fold.rows((*lower, (row,row)))
        all_images.add(q)
        actual = {v for s in support(q) for v in s}
        original = set()
        for i in range(64):
            if vertices & (1 << i):
                vertex = tuple(1 if i & (1 << j) else -1 for j in range(6))
                original.update(fold.carrier(vertex))
        assert actual == original
        if actual == all_names:
            full[q] += 1
    weights = Counter(len(q[-1][0]) for q in full)
    assert (len(all_images), sum(full.values()), len(full)) == (27, 30, 14)
    assert weights == {10: 5, 11: 5, 12: 3, 13: 1}
    print('148 cube slices give 27 tableaux; the 30 full occurrences give 14 distinct tableaux.')
    print('Full tableaux by tetrahedron count:', dict(sorted(weights.items())))
    if show:
        for i, q in enumerate(sorted(full),1):
            print(f'Slice {i} ({full[q]} occurrences): {q}')
    return full


def weak_three_skeleton(fold):
    """Present the signed simplices with common literal paths on both tetrahedron fronts."""
    ctx = Brackets(7)
    atoms = {(i,): v(i) for i in range(7)}

    def path(word):
        first, *rest = word
        return comp2(ctx.ctx, 0, atoms[first], path(rest)) if rest else atoms[first]

    def word(start, edges):
        remaining = set(edges)
        ordered = []
        while remaining:
            edge, = [e for e in remaining if fold.atom(e)[0][0] == (start,)]
            ordered.append(edge)
            remaining.remove(edge)
            start, = fold.atom(edge)[0][1]
        return tuple(ordered)

    def boundary_paths(s):
        rows = fold.atom(s)
        start, = rows[0][0]
        return tuple(word(start, edges) for edges in rows[1])

    def front(source, target, triangles):
        current = source
        remaining = set(triangles)
        route = None
        while remaining:
            enabled = []
            for triangle in remaining:
                before, after = boundary_paths(triangle)
                for j in range(len(current)-len(before)+1):
                    if current[j:j+len(before)] == before:
                        enabled.append((triangle, j, before, after))
            triangle, j, before, after = min(enabled)
            remaining.remove(triangle)
            left, right = current[:j], current[j+len(before):]
            step = atoms[triangle]
            if left:
                step = comp2(ctx.ctx, 0, path(left), step)
            if right:
                step = comp2(ctx.ctx, 0, step, path(right))
            initial = path(current)
            current = left + after + right
            final = path(current)
            if src(ctx.ctx, step) != initial:
                step = comp2(ctx.ctx, 1, kappa(ctx.ctx, initial, src(ctx.ctx, step)), step)
            if tgt(ctx.ctx, step) != final:
                step = comp2(ctx.ctx, 1, step, kappa(ctx.ctx, tgt(ctx.ctx, step), final))
            route = step if route is None else comp2(ctx.ctx, 1, route, step)
        assert current == target and route is not None
        return route

    for size in range(2, 5):
        for s in combinations(range(7), size):
            rows = fold.atom(s)
            if size == 2:
                a, b = (atoms[side[0]] for side in rows[0])
            elif size == 3:
                a, b = (path(w) for w in boundary_paths(s))
            else:
                start, end = boundary_paths(s)
                a, b = (front(start, end, side) for side in rows[2])
            atoms[s] = ctx.bracket(a,b)
            assert difference(ctx.ctx, a, b) == {atoms[f][1]: n for f,n in fold.d[s].items()}
    check_ctx(ctx.ctx)
    assert len(ctx.ctx) == 98
    print('98 raw declarations, including both typed fronts of all 35 tetrahedra.')
    return ctx.ctx, atoms


if __name__ == '__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('--slices', action='store_true', help='print the 14 complete strict tableaux')
    args = p.parse_args()
    fold = six_fold()
    degree = fold.check(6)
    assert degree == -1
    print('729 cube atoms, 127 simplex atoms, a strongly loop-free incidence order, degree -1.')
    check_states(fold, args.slices)
    weak_three_skeleton(fold)
