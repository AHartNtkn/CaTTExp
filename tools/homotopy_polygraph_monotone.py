"""Decide whole typed rings whose controls are monotone on each resource."""

from functools import cache
from itertools import combinations, product

from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form

from homotopy_polygraph_mask_catalogue import catalogue
from homotopy_polygraph_parking import acquisition_before_release
from homotopy_polygraph_two_resources import profiles


def reduced_axis(masks):
    return tuple(m for i, m in enumerate(masks) if i == 0 or masks[i-1] != m)


def feasible(chains, edges):
    successors = {x: [] for chain in chains for x in chain}
    degrees = dict.fromkeys(successors, 0)
    for a, b in (*edges, *(pair for chain in chains for pair in zip(chain, chain[1:]))):
        successors[a].append(b)
        degrees[b] += 1
    ready = [v for v, d in degrees.items() if not d]
    visited = 0
    while ready:
        v = ready.pop()
        visited += 1
        for w in successors[v]:
            degrees[w] -= 1
            if not degrees[w]:
                ready.append(w)
    return visited == len(degrees)


def choices(axes, resources):
    chains = [tuple((i, j) for j in range(len(row) - 1)) for i, row in enumerate(axes)]
    guards = []
    for r in range(resources):
        bit = 1 << r
        if any(all(m & bit for m in row) for row in axes):
            continue
        arrivals, departures = [], []
        for row, chain in zip(axes, chains):
            for a, b, event in zip(row, row[1:], chain):
                if (a ^ b) & bit:
                    (arrivals if b & bit else departures).append(event)
        guards.append(tuple(product(arrivals, departures)))
    return chains, guards


def cover_nerve(axes, resources):
    chains, guards = choices(axes, resources)
    vertices = [frozenset(w) for w in product(*guards) if feasible(chains, w)]
    # Every vertex of this nerve is a whole tuple of guard witnesses.
    @cache
    def possible(edges):
        return feasible(chains, edges)
    def extend(face, edges, start):
        for j in range(start, len(vertices)):
            combined = edges | vertices[j]
            if possible(combined):
                child = (*face, j)
                yield child
                yield from extend(child, combined, j + 1)
    if not vertices:
        return set()
    if possible(frozenset.union(*vertices)):
        return {(0,)}  # a full simplex
    return set(extend((), frozenset(), 0))


def witness_product(axes, resources, order):
    chains, guards = choices(axes, resources)
    if any(not pairs for pairs in guards):
        return []
    endpoints = {e for chain in chains for e in chain}
    base = frozenset((e,f) for e in endpoints for f in order.get(e, set()) & endpoints)
    factors = [sorted({pair[side] for pair in pairs}) for pairs in guards for side in (0,1)]
    subsets = [[s for n in range(1,len(f)+1) for s in combinations(f,n)] for f in factors]
    levels = []
    for cell in product(*subsets):
        edges = base.union(*(product(a,b) for a,b in zip(cell[::2],cell[1::2])))
        if feasible(chains,edges):
            degree = sum(len(s)-1 for s in cell)
            while len(levels) <= degree:
                levels.append([])
            levels[degree].append(cell)
    return levels


def product_boundary(cell):
    offset = 0
    for j, factor in enumerate(cell):
        if len(factor) >= 2:
            for k in range(len(factor)):
                yield cell[:j]+(factor[:k]+factor[k+1:],)+cell[j+1:], (-1)**(offset+k)
        offset += len(factor)-1


def integral_profile(faces):
    """Return H0 rank and positive-degree (Betti, torsion factors)."""
    if not faces:
        return 0, ()
    levels = [sorted(f for f in faces if len(f) == d)
              for d in range(1, max(map(len, faces)) + 1)]
    def boundary(cell):
        return [(cell[:k] + cell[k+1:], (-1)**k) for k in range(len(cell))]
    return cellular_profile(levels, boundary)


def cellular_profile(levels, boundary):
    """Integral cellular homology from oriented facets, by Smith reduction."""
    if not levels:
        return 0, ()
    ranks, torsion = [0], [()]
    for lower, upper in zip(levels, levels[1:]):
        indices = {f: i for i, f in enumerate(lower)}
        matrix = Matrix.zeros(len(lower), len(upper))
        for j, cell in enumerate(upper):
            for face, sign in boundary(cell):
                matrix[indices[face], j] = sign
        smith = smith_normal_form(matrix, domain=ZZ)
        diag = [abs(int(smith[i, i])) for i in range(min(smith.shape)) if smith[i, i]]
        ranks.append(len(diag))
        torsion.append(tuple(x for x in diag if x > 1))
    ranks.append(0)
    torsion.append(())
    groups = [(len(level) - ranks[k] - ranks[k+1], torsion[k+1]) for k, level in enumerate(levels)]
    assert not groups[0][1]
    higher = groups[1:]
    while higher and higher[-1] == (0, ()):
        higher.pop()
    return groups[0][0], tuple(higher)


@cache
def record_homology(axes, resources):
    return cellular_profile(witness_product(axes, resources, {}), product_boundary)


def whole_presentation(controls, resources):
    options = []
    for vertices, edges in controls:
        for r in range(resources):
            p, v = ('P', r), ('V', r)
            if acquisition_before_release(edges, p, v) or acquisition_before_release(edges, v, p):
                raise ValueError("a walk changes one resource in both directions")
        options.append(sorted({reduced_axis(a) for a in catalogue(vertices, edges, resources)}))
    checked = 0
    for axes in product(*options):
        checked += 1
        if record_homology(tuple(sorted(axes)), resources)[1]:
            return False, axes, checked
    return True, None, checked


def axes_at(programs, initial):
    states = profiles(programs, initial)
    return tuple(reduced_axis([sum(1 << r for r, count in counts.items() if not count)
                               for counts in row]) for row in states)


def incidence_record(rows, cols, missing):
    programs = [[] for _ in range(rows)] + [[('P', 0)] for _ in range(cols)]
    initial = [[int(i < rows)] for i in range(rows + cols)]
    for r, (a, b) in enumerate(missing, 1):
        programs[a].append(('P', r))
        programs[rows+b].append(('V', r))
        for i in range(rows + cols):
            initial[i].append(int(i != a))
    for word in programs[:rows]:
        word.append(('V', 0))
    return programs, initial


def check():
    # Integral chain matrices must see the order-two class of the projective plane.
    triangles = [(0,1,2),(1,2,3),(2,3,4),(0,3,4),(0,1,4),
                 (0,2,5),(1,3,5),(2,4,5),(0,3,5),(1,4,5)]
    faces = {f for tri in triangles for k in (1,2,3) for f in combinations(tri,k)}
    assert integral_profile(faces) == (1, ((0, (2,)),))

    for rows, expected in [(3, (1, ((1, ()),))), (4, (1, ()))]:
        programs, initial = incidence_record(rows, 3, [(i,i) for i in range(3)])
        axes = axes_at(programs, initial)
        assert integral_profile(cover_nerve(axes, 4)) == record_homology(axes, 4) == expected
        if rows == 4:
            initial[3][0] += 1  # retain the same word, suppress just its release witness
            assert record_homology(axes_at(programs, initial), 4) == (1, ((1, ()),))
    print('Integral witness nerve: triangle H1=Z, cone acyclic, increased apex hold H1=Z.')

    def control(word):
        return range(len(word)+1), [(i, op, i+1) for i, op in enumerate(word)]
    ab = [('P', 0), ('V', 1)]
    ba = [('P', 1), ('V', 0)]
    # Also exercise the opposite instruction order in one process.
    for words, expected in [([ab, ab, list(reversed(ba)), ()], True), ([ab, ab, ba, ba], False)]:
        passed, witness, checked = whole_presentation([control(w) for w in words], 2)
        assert passed == expected
        print(f'Whole presentation: {passed}; {checked} records examined; witness {witness}.')


if __name__ == '__main__':
    check()
