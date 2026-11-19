"""Check the ordered-partition trace to the extreme hom of a Gray cube."""
from collections import Counter, defaultdict
from functools import cache
from graphlib import TopologicalSorter
from itertools import combinations

from gray_globe_comparison import atom as cube_atom, boundary as cube_boundary
from gray_globe_comparison import close_atoms, face, strict_cells
from gray_globe_section import trim


@cache
def partitions(axes):
    if not axes:
        return ((),)
    return tuple((block,) + tail
                 for length in range(1, len(axes) + 1)
                 for block in combinations(axes, length)
                 for tail in partitions(tuple(i for i in axes if i not in block)))


def dimension(partition):
    return sum(len(block) - 1 for block in partition)


@cache
def orientation(partition):
    word = [i for block in partition for i in block[1:]]
    return (-1) ** sum(a > b for j, a in enumerate(word) for b in word[j + 1:])


@cache
def boundary(partition):
    result = {}
    preceding_degree = 0
    for j, block in enumerate(partition):
        for length in range(1, len(block)):
            for left in combinations(block, length):
                right = tuple(i for i in block if i not in left)
                facet = partition[:j] + (left, right) + partition[j + 1:]
                shuffle = sum(a > b for a in left for b in right)
                incidence = (-1) ** (preceding_degree + shuffle + length - 1)
                result[facet] = incidence * orientation(partition) * orientation(facet)
        preceding_degree += len(block) - 1
    return result


@cache
def perm_atom(partition):
    sides = []
    for sign in (-1, 1):
        chain = Counter([partition])
        rows = [(partition,)]
        for _ in range(dimension(partition)):
            differential = Counter()
            for generator, multiplicity in chain.items():
                for facet, incidence in boundary(generator).items():
                    differential[facet] += sign * multiplicity * incidence
            chain = +differential
            rows.append(tuple(sorted(chain.elements())))
        sides.append(rows[::-1])
    return tuple(zip(*sides))


@cache
def trace(partition):
    active = [j for j, block in enumerate(partition) if len(block) > 1]
    if len(active) > 1:
        return ()
    n = sum(map(len, partition))
    result = []
    crossed = set()
    for j, block in enumerate(partition):
        if not active or j == active[0]:
            result.append(tuple((1, 2) if i in block else (0, int(i in crossed))
                                for i in range(n)))
        crossed.update(block)
    return tuple(result)


def corners(n):
    return tuple((((0, side),) * n,) for side in (0, 1))


def image(tableau, n):
    def row(chain):
        return tuple(sorted(g for p in chain for g in trace(p)))
    return (corners(n),) + tuple((row(s), row(t)) for s, t in tableau)


def forget(partition, last):
    """Cellular projection on chains, vanishing on dimension drops."""
    if (last,) in partition:
        return tuple(block for block in partition if block != (last,))
    return None


def check_complex(n):
    axes = tuple(range(n))
    order = TopologicalSorter()
    for p in partitions(axes):
        order.add(p)
        assert all(len(row) == 1 for row in perm_atom(p)[0])
        cube_chain = Counter()
        for g in trace(p):
            cube_chain.update(cube_boundary(g))
        projected_boundary = Counter()
        traced_boundary = Counter()
        for q, incidence in boundary(p).items():
            after, before = (p, q) if incidence < 0 else (q, p)
            order.add(after, before)
            for g in trace(q):
                traced_boundary[g] += incidence
            dropped = forget(q, n - 1)
            if dropped is not None:
                projected_boundary[dropped] += incidence
        if dimension(p):
            assert traced_boundary == cube_chain
        else:
            a, b = corners(n)
            assert cube_chain == Counter({a[0]: -1, b[0]: 1})
        if n > 1:
            dropped = forget(p, n - 1)
            assert projected_boundary == (Counter(boundary(dropped)) if dropped else Counter())
            cube_projection = Counter(g[:-1] for g in trace(p) if g[-1][0] == 0)
            assert cube_projection == (Counter(trace(dropped)) if dropped else Counter())
    assert len(tuple(order.static_order())) == len(partitions(axes))
    assert image(perm_atom((axes,)), n) == cube_atom(((1, 2),) * n)
    print(f'{n} axes: {len(partitions(axes))} faces; chain, order and atom checks passed')


def four_cube_section():
    n = 4
    axes = tuple(range(n))
    top = perm_atom((axes,))
    sources = close_atoms(map(perm_atom, partitions(axes)), n - 1)
    targets = {trim(y) for y in strict_cells((1,) * n, n) if y[0] == corners(n)}
    choices = defaultdict(set)
    for padded in sources:
        x = trim(padded)
        y = trim(image(x, n))
        if len(y) == len(x) + 1:
            choices[y].add(x)
    assert set(choices) == targets
    choices[image(top, n)] = {top}
    constraints = [(y, trim(face(y, s)), s) for y in targets if len(y) > 2 for s in (0, 1)]

    @cache
    def selected_face(x, side):
        return trim(face(x, side))

    def solve(domains):
        while True:
            changed = False
            for y, f, s in constraints:
                images = domains[f] & {selected_face(x, s) for x in domains[y]}
                if not images:
                    return None
                valid = {x for x in domains[y] if selected_face(x, s) in images}
                if valid != domains[y] or images != domains[f]:
                    domains[y], domains[f] = valid, images
                    changed = True
            if not changed:
                break
        ambiguous = [y for y in targets if len(domains[y]) > 1]
        if not ambiguous:
            return {y: next(iter(xs)) for y, xs in domains.items()}
        y = min(ambiguous, key=lambda cell: (len(domains[cell]), len(cell), cell))
        for x in sorted(domains[y]):
            result = solve({**domains, y: {x}})
            if result is not None:
                return result
        return None

    section = solve(choices)
    assert section is not None and section[image(top, n)] == top
    for y, x in section.items():
        assert image(x, n) == y
    for y, f, side in constraints:
        # Pad back to the literal face dimension, including identities.
        x = section[f]
        assert x + (((), ()),) * (len(section[y]) - 1 - len(x)) == face(section[y], side)
    print(f'4-cube: pinned globular section on all {len(targets)} cells up to identities')


def read_face(word):
    return tuple((1, 2) if c == '*' else (0, int(c)) for c in word)


def path_chain(word):
    crossed = set()
    result = []
    for digit in word:
        axis = int(digit)
        result.append(tuple((1, 2) if i == axis else (0, int(i in crossed))
                            for i in range(len(word))))
        crossed.add(axis)
    return tuple(sorted(result))


def lift_by_rewrites(start, end, negative, positive, cubes, square=None, outer_first=None):
    """Reachability allowing both directions at every other thin square."""
    n = len(start)

    def event(permutation, position, width):
        crossed = permutation[:position]
        moving = permutation[position:position + width]
        return ''.join('1' if i in crossed else '*' if i in moving else '0'
                       for i in range(n))

    def execute(permutation, i):
        a, b = permutation[i:i + 2]
        assert a > b
        return permutation[:i] + (b, a) + permutation[i + 2:]

    def serializations(permutation, labels):
        if not labels:
            assert permutation == end
            yield ()
        for i, (a, b) in enumerate(zip(permutation, permutation[1:])):
            label = event(permutation, i, 2)
            if a > b and label in labels:
                for tail in serializations(execute(permutation, i), labels - {label}):
                    yield (i,) + tail

    def neighbors(word, remaining):
        permutation = start
        for t, i in enumerate(word[:-1]):
            j = word[t + 1]
            if abs(i - j) > 1:
                left, right = sorted((i, j))
                blocks = (tuple((a,) for a in permutation[:left])
                          + (tuple(sorted(permutation[left:left + 2])),)
                          + tuple((a,) for a in permutation[left + 2:right])
                          + (tuple(sorted(permutation[right:right + 2])),)
                          + tuple((a,) for a in permutation[right + 2:]))
                # In both witnesses the first two blocks are the nested pairs;
                # "outer first" describes the order BEFORE the interchange.
                if blocks != square or (i == left) == outer_first:
                    yield word[:t] + (j, i) + word[t + 2:], remaining
            if j == i + 1 and word[t + 2:t + 3] == (i,):
                label = event(permutation, i, 3)
                if label in remaining:
                    yield word[:t] + (j, i, j) + word[t + 3:], remaining - {label}
            permutation = execute(permutation, i)

    ends = set(serializations(start, positive))
    todo = [(word, cubes) for word in serializations(start, negative)]
    seen = set(todo)
    assert todo and ends
    while todo:
        word, remaining = todo.pop()
        if not remaining and word in ends:
            return True
        for state in neighbors(word, remaining):
            if state not in seen:
                seen.add(state)
                todo.append(state)
    return False


def five_cube_obstruction():
    n = 5
    axes = tuple(range(n))
    targets = {y for y in strict_cells((1,) * n, 3) if y[0] == corners(n)}
    sources = close_atoms((perm_atom(p) for p in partitions(axes) if dimension(p) <= 2), 2)
    images = {image(x, n) for x in sources}
    assert images <= targets
    assert (len(sources), len(targets), len(targets - images)) == (183212, 7752, 14)
    print(f'5-cube: {len(sources)} source 2-cells, {len(images)}/{len(targets)} images')

    def path_order(edges):
        remaining = set(edges)
        order = []
        while remaining:
            edge, = (g for g in remaining if {i for i, tag in enumerate(g) if tag == (0, 1)}
                     == set(order))
            axis, = (i for i, tag in enumerate(edge) if tag == (1, 2))
            order.append(axis)
            remaining.remove(edge)
        return tuple(order)

    def labels(row):
        result = frozenset(''.join('*' if d else str(t) for d, t in g) for g in row)
        assert len(result) == len(row)
        return result

    for y in targets - images:
        assert lift_by_rewrites(path_order(y[1][0]), path_order(y[1][1]),
                                labels(y[2][0]), labels(y[2][1]), labels(y[3][0]))
    print('5-cube: two-way interchanges lift all 14 remaining cells')

    cases = [
        ('43210', '03124', '000** 00*1* 0*11* 0**10 *00*0 *111* *1*10 **010',
         '100** 10*1* 1*11* 1**10 *000* *00*1 *0*11 **111', '*00** *0*1* **11* ***10',
         ((0, 3), (1, 2), (4,)), False),
        ('41320', '01234', '**000 *1*00 *11*0 *111* 0*00* 01**0 01*1* 010**',
         '**001 *000* *1*01 *11*1 01**1 1*00* 11*0* 111**', '**00* *1*0* *11** 01***',
         ((1, 4), (2, 3), (0,)), True),
    ]
    for start, end, neg, pos, top, square, required in cases:
        def chain(words):
            return tuple(sorted(map(read_face, words.split())))
        cubes = chain(top)
        witness = (corners(n), (path_chain(start), path_chain(end)),
                   (chain(neg), chain(pos)), (cubes, cubes))
        assert witness in targets
        if not required:
            assert witness not in images
        for outer_first in (False, True):
            allowed = lift_by_rewrites(tuple(map(int, start)), tuple(map(int, end)),
                                       frozenset(neg.split()), frozenset(pos.split()),
                                       frozenset(top.split()), square, outer_first)
            assert allowed == (outer_first == required)
        print(f'{start} to {end}: only ' + ('outer' if required else 'inner')
              + '-pair-first to the reverse order can lift the 3-cell')


if __name__ == '__main__':
    for size in range(1, 7):
        check_complex(size)
    four_cube_section()
    five_cube_obstruction()
