"""Test the cube degree formula and the seven-state nerve certificate."""
from collections import Counter
from itertools import combinations, product

from relative_coherence_simplex_carrier import flags, orientation
from relative_coherence_state_colours import inventory, mask


def colourings(size, colours, prefix=(0,)):
    if len(prefix) == size:
        if max(prefix) + 1 == colours:
            yield prefix
        return
    for c in range(min(colours, max(prefix) + 2)):
        yield from colourings(size, colours, (*prefix, c))


def dual_degree(omissions, k):
    # Coefficient of the oriented face [1,...,k] in the dual fundamental cycle.
    degree = 0
    for sides in product((0, 1), repeat=k):
        image = [omissions[2*j + s] for j, s in enumerate(sides)]
        if 0 not in image and len(set(image)) == k:
            degree += (-1)**sides.count(0) * orientation(image)
    return degree


def tree(edges, k):
    component = list(range(k+1))
    for a, b in edges:
        i, j = component[a], component[b]
        if i == j:
            return False
        component = [j if c == i else c for c in component]
    return len(set(component)) == 1


def check_degrees(k):
    counts = Counter()
    choices = 0
    staircases = list(flags(range(k)))
    for colour in colourings(2**k, k+1):
        allowed = [sorted(set(range(k+1)) -
                          {c for x, c in enumerate(colour) if x >> j & 1 == s})
                   for j in range(k) for s in (0, 1)]
        if not all(allowed):
            continue
        degree = 0
        for simplex, sign in staircases:
            names = tuple(colour[x] for x in simplex)
            if len(set(names)) == k+1:
                degree += sign * orientation(names)
        counts[abs(degree)] += 1
        for labels in product(*allowed):
            choices += 1
            assert abs(dual_degree(labels, k)) == abs(degree)
            assert abs(degree) == int(tree(zip(labels[::2], labels[1::2]), k))
    print(f'Dimension {k}: {dict(sorted(counts.items()))} proper surjections by absolute degree, '
          f'{choices} choices of omitted labels (up to relabelling the vertex colouring).')


def seven_state_certificate():
    _, carriers, _ = inventory()
    selected = [2, 12, 32, 77, 83, 105, 130]
    stars = [tuple([2*j + (x >> j & 1) for j in range(6)] +
                   [12+j for j, i in enumerate(selected) if carriers[i][0] >> x & 1])
             for x in range(64)]
    faces = sorted({f for star in stars for f in combinations(star, 6)})
    cofaces = sorted({f for star in stars for f in combinations(star, 7)})
    index = {f: i for i, f in enumerate(faces)}
    boundary = [mask(index[f] for f in combinations(g, 6)) for g in cofaces]
    sphere = mask(index[star[:6]] for star in stars)
    assert sphere.bit_count() == 64
    pivots = {}

    def reduce(column, witness):
        while column:
            pair = pivots.get(column.bit_length()-1)
            if pair is None:
                break
            column ^= pair[0]
            witness ^= pair[1]
        return column, witness

    for j, column in enumerate(boundary):
        reduced, witness = reduce(column, 1 << j)
        if reduced:
            pivots[reduced.bit_length()-1] = (reduced, witness)
    remainder, witness = reduce(sphere, 0)
    assert remainder == 0
    chain = [g for j, g in enumerate(cofaces) if witness >> j & 1]
    actual = Counter(f for g in chain for f in combinations(g, 6))
    assert {f for f, n in actual.items() if n % 2} == {star[:6] for star in stars}
    print(f'Seven states {selected}: {len(faces)} five-simplices, {len(cofaces)} six-simplices; '
          f'{len(chain)} columns have exactly the 64 boundary facets modulo two.')


if __name__ == '__main__':
    check_degrees(2)
    check_degrees(3)
    seven_state_certificate()
