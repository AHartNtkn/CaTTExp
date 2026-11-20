"""Decide signed degree for arbitrary protected states by testing only vertices, edges and squares."""
from argparse import ArgumentParser
from collections import Counter
from functools import reduce
from itertools import combinations, product

from relative_coherence_cube_boundary import boundary
from relative_coherence_orbit_permissions import minimal_sets
from relative_coherence_simplex_carrier import facets
from relative_coherence_state_colours import mask, priority_colours
from relative_coherence_state_symmetries import classify
from relative_coherence_steiner_cuts import tableau


def vertices(face):
    low = mask(i for i, value in enumerate(face) if value == 1)
    free = [i for i,x in enumerate(face) if x == 0]
    return [low | mask(comb) for j in range(len(free)+1) for comb in combinations(free, j)]


def carriers(verts, supports):
    wanted = mask(verts)
    return mask(i for i,s in enumerate(supports) if not wanted & ~s)


def obstructions(face):
    """Return a support clause as its alternative simplices, and its colouring."""
    vs = vertices(face)
    axes = tuple(i for i,x in enumerate(face) if x == 0)
    early = tuple(i for i in range(len(face)) if i not in axes)
    if len(axes) <= 1:
        yield (tuple(vs),), vs[0], early + axes
    else:
        a,b,c,d = vs
        for first in ((a,b,d), (a,c,d)):
            for second in ((b,a,c), (b,d,c)):
                root, other = sorted(set(first) & set(second))
                last = (root ^ other).bit_length()-1
                penultimate, = [i for i in axes if i != last]
                yield (first, second), root, early + (penultimate, last)


def transversals(constraints):
    # At each stage the stored sets are all inclusion-minimal hitting sets.
    kept = {0}
    for c in constraints:
        options = [1<<i for i in range(c.bit_length()) if c >> i & 1]
        candidates = {p|bit for p in kept if not p & c for bit in options}
        kept = {p for p in kept if p & c}
        for p in sorted(candidates, key=int.bit_count):
            q = (p-1) & p
            while q and q not in kept:
                q = (q-1) & p
            if not q:
                kept.add(p)
    return kept


def cone(vertex, cycle):
    chain = Counter()
    for s, n in cycle.items():
        if vertex not in s:
            sign = (-1)**sum(v < vertex for v in s)
            chain[tuple(sorted((vertex, *s)))] += sign*n
    return {s:n for s,n in chain.items() if n}


def integral_carrier(selected, faces, common):
    chosen = {}
    for f in faces:
        vs = vertices(f)
        dim = f.count(0)
        if not dim:
            chain = {(vs[0],): 1}
        else:
            target = Counter()
            for subface, sign in boundary(f):
                target.update({s:sign*n for s,n in chosen[subface].items()})
            if dim >= 3:
                apex = next(v for v in vs if common >> v & 1)
            elif dim == 2:
                a,b,c,d = vs
                apex = next(v for v,triangles in
                            ((a, ((a,b,d),(a,c,d))), (b, ((b,a,c),(b,d,c))))
                            if all(carriers(t, selected) for t in triangles))
            else:
                apex = vs[0]
            chain = cone(apex, target)
            signed_boundary = Counter()
            for simplex, n in chain.items():
                signed_boundary.update({t:sign*n for t,sign in facets(simplex)})
            assert signed_boundary == target
        assert all(set(s) <= set(vs) and carriers(s, selected) for s in chain)
        chosen[f] = chain
    return len(chosen[(0,)*6])


def check_common_rows(n):
    rank = n-4
    rows = tableau((0,)*n)[rank]
    actual = {v for side in rows for face in side for v in vertices(face)}
    transitions = (1 << (n-1))-1
    assert actual == {v for v in range(1 << n) if ((v ^ (v>>1)) & transitions).bit_count() <= rank}
    assert all(any(v in actual for v in vertices(f)) for f in product((-1,0,1), repeat=n) if f.count(0) == 3)


def main(show_lists):
    for width in range(4, 10):
        check_common_rows(width)
    classes, state_carriers, priority = classify()
    supports = [s for s,_ in state_carriers]
    common = reduce(int.__and__, supports)
    assert common == mask(v for v in range(64) if ((v ^ (v>>1)) & 31).bit_count() <= 2)
    faces = sorted(product((-1,0,1), repeat=6), key=lambda f: f.count(0))
    no_common = Counter(f.count(0) for f in faces if not common & mask(vertices(f)))
    assert no_common == {0:32, 1:60, 2:30}
    positive = [mask(v for v in range(64) if v >> i & 1) for i in range(6)]
    clauses = set()
    checked = 0
    for f in faces:
        if f.count(0) > 2:
            continue
        for alternatives, root, order in obstructions(f):
            clause = reduce(int.__or__, (carriers(t,supports) for t in alternatives))
            colours = priority_colours(root, order, positive)
            full = mask(i for i,s in enumerate(supports) if all(s & c for c in colours))
            assert not full & ~clause and full in priority
            clauses.add(clause)
            checked += 1
    named = minimal_sets(clauses)
    assert checked == 1216 and set(named) == set(minimal_sets(priority)) and len(named) == 72
    group_masks = list(map(mask, classes))
    projected = minimal_sets({mask(i for i,g in enumerate(group_masks) if g & c) for c in named})
    assert len(projected) == 16
    minimal_failures = transversals(projected)
    assert Counter(s.bit_count() for s in minimal_failures) == {2:4, 3:863, 4:5002}
    print(f'{checked} local clauses give {len(named)} named and {len(projected)} projected minimal permissions.')
    if show_lists:
        for p in projected:
            print('Sufficient class representatives:', [c[0] for i,c in enumerate(classes) if p >> i & 1])
    print('All inclusion-minimal protections by class count:', dict(sorted(Counter(s.bit_count() for s in minimal_failures).items())))
    for p in sorted(minimal_failures):
        if p.bit_count() == 2:
            selected = [supports[j] for i,c in enumerate(classes) if p >> i & 1 for j in c]
            print('Integral top chain for classes', [c[0] for i,c in enumerate(classes) if p >> i & 1],
                  'has', integral_carrier(selected, faces, common), 'simplices.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--lists', action='store_true')
    main(parser.parse_args().lists)
