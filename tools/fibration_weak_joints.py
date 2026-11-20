"""Compute nonabelian path tests for finite comparison-fibre order complexes."""

from collections import deque
from itertools import combinations

from homotopy_polygraph_timed_charts import order_complex_betti
from homotopy_polygraph_two_changes import comparison_poset, lower_charts, presentation


def inverse(word):
    return tuple(-i for i in reversed(word))


def reduce_word(word):
    out = []
    for i in word:
        if out and out[-1] == -i:
            out.pop()
        else:
            out.append(i)
    return tuple(out)


def eliminate(word, generator, replacement):
    out = []
    for i in word:
        if abs(i) == generator:
            out.extend(replacement if i > 0 else inverse(replacement))
        else:
            out.append(i)
    return reduce_word(out)


class FibreGroup:
    """Collapse a spanning tree and eliminate generators with a defining relation."""

    def __init__(self, elements, below):
        size = len(elements)
        edges = [(i, j) for i, j in combinations(range(size), 2)
                 if below(elements[i], elements[j]) or below(elements[j], elements[i])]
        neighbors = [[] for _ in elements]
        for i, j in edges:
            neighbors[i].append(j)
            neighbors[j].append(i)
        seen, queue, tree = {0}, deque([0]), set()
        while queue:
            i = queue.popleft()
            for j in neighbors[i]:
                if j not in seen:
                    seen.add(j)
                    tree.add(tuple(sorted((i, j))))
                    queue.append(j)
        if len(seen) != size:
            raise ValueError('Choose a single nonempty component')
        self.arcs = {}
        generators = set()
        for i, j in edges:
            word = ()
            if (i, j) not in tree:
                g = len(generators) + 1
                generators.add(g)
                word = (g,)
            self.arcs[i, j], self.arcs[j, i] = word, inverse(word)
        relations = []
        for i, j, k in combinations(range(size), 3):
            if all(pair in self.arcs for pair in ((i, j), (j, k), (k, i))):
                relations.append(self.walk((i, j, k, i)))
        while True:
            relations = sorted({r for r in relations if r}, key=lambda r: (len(r), r))
            choice = next(((r, i) for r in relations for i in r
                           if r.count(i) + r.count(-i) == 1), None)
            if choice is None:
                break
            r, i = choice
            k = r.index(i)
            rest = r[k + 1:] + r[:k]
            # Cyclically permute the relator to i * rest = 1.
            replacement = inverse(rest) if i > 0 else rest
            generators.remove(abs(i))
            relations = [eliminate(s, abs(i), replacement) for s in relations]
            self.arcs = {e: eliminate(w, abs(i), replacement) for e, w in self.arcs.items()}
        self.generators, self.relations = generators, relations

    def walk(self, vertices):
        return reduce_word(i for edge in zip(vertices, vertices[1:]) for i in self.arcs[edge])


def main():
    presentation()
    elements, below = comparison_poset()
    sphere = FibreGroup(elements, below)
    assert not sphere.generators and not sphere.relations
    betti = order_complex_betti(elements, below)
    assert betti[:3] == (1, 0, 1)
    print(f'Two changing sides: {len(elements)} objects, trivial fundamental group, b2={betti[2]}.')

    model, component = lower_charts('CD')
    cells = sorted(component)
    circle = FibreGroup(cells, lambda x, y: x != y and y in model.ideal(x))
    assert len(circle.generators) == 1 and not circle.relations
    # Traverse the actual two binary exchanges in opposite directions.
    serial = [i for i, c in enumerate(cells) if model.degrees[c] == 0]
    joint = [i for i, c in enumerate(cells) if model.degrees[c] == 1]
    a, b = serial
    p, q = joint
    lap = (a, p, b, q, a)
    assert len(circle.walk(lap)) == 1
    for m in range(-4, 5):
        for n in range(-4, 5):
            first = (lap if m >= 0 else lap[::-1])[1:] * abs(m)
            second = (lap if n >= 0 else lap[::-1])[1:] * abs(n)
            assert (circle.walk((a,) + first) == circle.walk((a,) + second)) == (m == n)
    print('Middle-wire circle: 81 pairs of based structural paths, exactly 9 glue relative to both poles.')


if __name__ == '__main__':
    main()
