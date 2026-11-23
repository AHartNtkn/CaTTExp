"""Test configuration expansion along forests, including births and their clocks."""
from argparse import ArgumentParser
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path

from semistrict_surface_configuration_blocks import Graph, check_attachment, path_at, subsets


def graph(order, level):
    return Graph(tuple(order), tuple((*e, level) for e in combinations(sorted(order), 2)))


def substitute(outer, fibres):
    order = tuple(x for i in outer.order for x in fibres[i].order)
    parent = {x: i for i in outer.order for x in fibres[i].order}
    levels = {(i, j): h for i, j, h in outer.levels}
    inner = {(a, b): h for i in outer.order for a, b, h in fibres[i].levels}
    for a, b in combinations(sorted(order), 2):
        i, j = parent[a], parent[b]
        if i != j:
            inner[a, b] = levels[tuple(sorted((i, j)))]
    return Graph(order, tuple((*e, h) for e, h in sorted(inner.items())))


@dataclass(frozen=True)
class Expansion:
    fibres: tuple  # One (root, graph on its leaves) for each named root.

    def apply(self, data, chain, fraction, quantile):
        projected = []
        for names, weight in chain:
            roots = frozenset(i for i, g in self.fibres if names.intersection(g.order))
            if projected and projected[-1][0] == roots:
                projected[-1] = roots, projected[-1][1] + weight
            else:
                projected.append((roots, weight))
        clock, value = data(tuple(projected), fraction, quantile)
        at_end = {i: g.restrict(chain[-1][0]) for i, g in self.fibres}
        return clock, substitute(value, at_end)

    def compose(self, inner):
        # The result is still indexed by the outer roots.
        return Expansion(tuple((root, substitute(g, dict(inner.fibres))) for root, g in self.fibres))

    def lift(self, data):
        return lambda chain, t, q: self.apply(data, chain, t, q)


def expansion(sources, targets, assignment):
    fibres = tuple((i, graph([s for s, t in zip(sources, assignment, strict=True) if t == i][::-1], i % 3))
                   for i in targets)
    return Expansion(fibres)


def check_composition():
    # Read a two-stage forest with a merge or a birth in either stage.
    original, middle, leaves = (7, 9), (2, 3, 4), (0, 1, 5)
    sets = subsets(leaves)
    chains = [((s, Fraction(1, 3)), (t, Fraction(2, 3))) for s in sets for t in sets if t <= s]
    def input_path(chain, t, q):
        return path_at(chain, original, t, q)
    count = births = 0
    for first in product(original, repeat=len(middle)):
        f = expansion(middle, original, first)
        for second in product(middle, repeat=len(leaves)):
            g = expansion(leaves, middle, second)
            composite = f.compose(g)
            for chain in chains:
                for t, q in ((Fraction(1, 3), Fraction(1, 5)), (Fraction(1, 4), Fraction(1, 2))):
                    nested = g.apply(f.lift(input_path), chain, t, q)
                    assert nested == composite.apply(input_path, chain, t, q)
                    if not chain[-1][0]:
                        assert nested[0] > 0 and nested[1] == Graph((), ())
                        births += 1
                    count += 1
    return count, births


def retract(names, members, root, vertex):
    return Expansion(tuple((i, vertex if i == root else graph(() if i in members else (i,), 0))
                           for i in sorted(names)))


def check_stationary_intersections():
    names = frozenset(range(4))
    candidates = [s for s in subsets(names) if len(s) >= 2]
    count = 0
    for left, right in combinations(candidates, 2):
        for root in sorted(left & right):
            for a, b in product(range(3), repeat=2):
                li = retract(names, left, root, graph(sorted(left, reverse=True), a))
                ri = retract(names, right, root, graph(sorted(right), b))
                both = li.compose(ri)
                union_vertex = dict(both.fibres)[root]
                assert set(union_vertex.order) == left | right
                assert both == retract(names, left | right, root, union_vertex)
                assert both.compose(both) == both
                count += 1
    return count


def check_rice(checkout):
    base = '(x : *) (a : id(id(x)) -> id(id(x))) (m : comp[a,a] -> a)'
    left = 'comp[comp[[m],a],m]'
    # The 5-generators have a 4-boundary which uses a compound merge.
    check_attachment(checkout, left, base)
    birth_base = base + ' (e : id(id(id(x))) -> a)'
    born = 'comp[comp[a,[e]],m]'
    check_attachment(checkout, f'id({born})', birth_base)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    print('Expanded path values and positive empty clocks:', *check_composition())
    print('Overlapping inflation idempotents:', check_stationary_intersections())
    if args.catt_strict:
        check_rice(args.catt_strict.resolve())
        print('Literal degree-six and degree-seven attachments checked.')
