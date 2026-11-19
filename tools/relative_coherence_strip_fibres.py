"""Enumerate named cube chains and their projections for Researcher Response 7.

Uppercase letters are distinct top occurrences. Lowercase letters are unary
lower gates. A tier stores its entire marked word on each lane.
"""
from collections import Counter
from functools import cache
from itertools import combinations, permutations, product


def events(tier):
    return frozenset(ch for word in tier for ch in word if ch.isupper())


def substitute(tier, rules, keep, side):
    return tuple("".join(rules[ch][i][side] if ch.isupper() and ch not in keep else ch
                         for ch in word)
                 for i, word in enumerate(tier))


def lane_charts(word, order, rules, lane):
    if not order:
        yield word
        return
    event, *rest = order
    source = rules[event][lane][0]
    for k in range(len(word) - len(source) + 1):
        if word.startswith(source, k):
            for tail in lane_charts(word[k + len(source):], rest, rules, lane):
                yield word[:k] + event + tail


def chains(initial, final, rules, well_typed=None):
    @cache
    def visit(state, remaining):
        if not remaining:
            return {()} if state == final else set()
        result = set()
        for size in range(1, len(remaining) + 1):
            for block in combinations(sorted(remaining), size):
                charts = set()
                for order in permutations(block):
                    words = [lane_charts(word, [x for x in order if i in rules[x]], rules, i)
                             for i, word in enumerate(state)]
                    charts.update(product(*words))
                for tier in charts:
                    if well_typed is not None and not well_typed(tier):
                        continue
                    after = substitute(tier, rules, (), 1)
                    for suffix in visit(after, remaining.difference(block)):
                        result.add((tier,) + suffix)
        return result
    return visit(initial, frozenset(rules))


def boundary(cell, rules):
    for i, tier in enumerate(cell):
        names = events(tier)
        for size in range(1, len(names)):
            for first in combinations(sorted(names), size):
                cut = (substitute(tier, rules, first, 0),
                       substitute(tier, rules, names.difference(first), 1))
                yield cell[:i] + cut + cell[i + 1:]


class Complex:
    def __init__(self, initial, final, rules, well_typed=None):
        self.cells = sorted(chains(initial, final, rules, well_typed))
        index = {cell: i for i, cell in enumerate(self.cells)}
        self.facets = [tuple(index[face] for face in boundary(cell, rules)) for cell in self.cells]
        self.degrees = [len(rules) - len(cell) for cell in self.cells]
        neighbors = [set(faces) for faces in self.facets]
        for i, faces in enumerate(self.facets):
            for j in faces:
                neighbors[j].add(i)
        self.components = []
        remaining = set(range(len(self.cells)))
        while remaining:
            seed = remaining.pop()
            component, stack = {seed}, [seed]
            while stack:
                new = neighbors[stack.pop()] & remaining
                component.update(new)
                stack.extend(new)
                remaining.difference_update(new)
            self.components.append(component)
        self.index = index

    def betti(self, cells):
        ranks, sizes = Counter(), Counter()
        basis = {}
        for i in sorted(cells):
            degree = self.degrees[i]
            sizes[degree] += 1
            column = 0
            for face in self.facets[i]:
                column ^= 1 << face
            while column:
                pivot = column.bit_length()
                if pivot not in basis:
                    basis[pivot] = column
                    ranks[degree] += 1
                    break
                column ^= basis[pivot]
        result = [sizes[j] - ranks[j] - ranks[j + 1] for j in range(max(sizes) + 1)]
        while len(result) > 1 and not result[-1]:
            result.pop()
        return tuple(result)

    def ideal(self, i):
        result, stack = {i}, [i]
        while stack:
            for j in self.facets[stack.pop()]:
                if j not in result:
                    result.add(j)
                    stack.append(j)
        return result


def restrict_rules(rules, lanes):
    return {event: {j: faces[i] for j, i in enumerate(lanes) if i in faces}
            for event, faces in rules.items() if any(i in faces for i in lanes)}


def project(cell, lanes):
    tiers = [tuple(tier[i] for i in lanes) for tier in cell]
    return tuple(tier for tier in tiers if events(tier))


def separator_orders(local, component, shared):
    orders = set()
    for index in component:
        projected = [events(tier) & shared for tier in local.cells[index]]
        if any(len(block) > 1 for block in projected):
            return set()
        orders.add(tuple(next(iter(block)) for block in projected if block))
    return orders


def audit(initial, final, rules, blocks, expected, separator=True):
    whole = Complex(initial, final, rules)
    local = [Complex(tuple(initial[i] for i in block), tuple(final[i] for i in block),
                     restrict_rules(rules, block)) for block in blocks]
    images = [tuple(x.index[project(cell, b)] for x, b in zip(local, blocks))
              for cell in whole.cells]
    observed = sorted(whole.betti(component) for component in whole.components)
    assert observed == sorted(expected)
    checked = 0
    if separator:
        for selected in product(*(x.components for x in local)):
            inverse = {i for i, point in enumerate(images)
                       if all(v in component for v, component in zip(point, selected))}
            if not inverse:
                continue
            assert inverse in whole.components
            for j in range(len(blocks) - 1):
                shared = set(restrict_rules(rules, blocks[j])) & set(restrict_rules(rules, blocks[j + 1]))
                left = separator_orders(local[j], selected[j], shared)
                right = separator_orders(local[j + 1], selected[j + 1], shared)
                assert len(left) == 1 and left == right
            for point in product(*selected):
                ideals = [x.ideal(v) for x, v in zip(local, point)]
                preimage = {i for i in inverse if all(v in ideal for v, ideal in zip(images[i], ideals))}
                assert preimage and whole.betti(preimage) == (1,)
                checked += 1
    else:
        assert all(len(x.components) == 1 and max(x.degrees) == 1 for x in local)
    print("cells", len(whole.cells), "Betti numbers", observed, "local tuples checked", checked)
    return whole


def main():
    # The central lane of an event is its private gate. At a seam the
    # left event can erase a letter and its right neighbour can insert one.
    for both_idle in (False, True):
        names = "ABCD" if both_idle else "ABCDE"
        n = len(names)
        rules = {}
        source, target = [], []
        for i, x in enumerate(names):
            rules[x] = {2 * i: ("a", "b")}
            source.append("a")
            target.append("b")
            if i + 1 < n:
                rules[x][2 * i + 1] = ("", "") if both_idle else ("d", "")
                source.append("" if both_idle else "d")
                target.append("" if both_idle else "e")
            if i:
                rules[x][2 * i - 1] = ("", "") if both_idle else ("", "e")
        audit(tuple(source), tuple(target), rules, [(i,) for i in range(len(source))],
              [(1, 3, 3, 1) if both_idle else (1,)])

    # Two shared events cross the cut in a strictly forced order, while
    # the two independent events can occur anywhere on their own lane.
    rules = {"A": {0: ("a", "b"), 1: ("a", "b")},
             "B": {0: ("b", "c"), 1: ("b", "c")},
             "C": {0: ("d", "e")}, "D": {1: ("d", "e")}}
    audit(("ad", "da"), ("ce", "ec"), rules, [(0,), (1,)], [(1,)])

    # Two lanes in one strip: C sees an empty source on the first and a
    # two-letter source on the second. A links this strip to the last lane.
    rules = {"A": {0: ("a", "b"), 1: ("a", "b"), 2: ("a", "b")},
             "C": {0: ("", "x"), 1: ("de", "f")},
             "D": {2: ("p", "q")}}
    audit(("a", "ade", "pa"), ("bx", "bf", "qb"), rules, [(0, 1), (2,)], [(1,)])

    # Without the separator hypothesis each lane admits an exchange, but
    # opposite spatial orders prevent those exchanges from gluing.
    rules = {"A": {0: ("a", "b"), 1: ("a", "b")},
             "B": {0: ("c", "d"), 1: ("c", "d")}}
    audit(("ac", "ca"), ("bd", "db"), rules, [(0,), (1,)], [(1,), (1,)], False)


if __name__ == "__main__":
    main()
