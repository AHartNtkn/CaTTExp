"""Test signed degree certificates after identifying cubical states by signed isomorphism."""
from collections import Counter
from itertools import combinations

from relative_coherence_facet_omissions import integral_nerve_certificate
from relative_coherence_simplex_carrier import flags, orientation
from relative_coherence_state_colours import mask, priority_colours
from relative_coherence_state_symmetries import classify


def minimal_sets(family):
    result = []
    for x in sorted(family, key=lambda x: (x.bit_count(), x)):
        if not any(y & x == y for y in result):
            result.append(x)
    return result


def solve():
    classes, carriers, choices = classify()
    positive = [mask(v for v in range(64) if v >> i & 1) for i in range(6)]
    orbits = [mask(group) for group in classes]
    def project(states):
        return mask(i for i, group in enumerate(orbits) if group & states)
    degree_one = {project(s): witness for s, witness in choices.items()}
    sufficient = minimal_sets(degree_one)
    paths = tuple(flags(range(6)))
    staircase = []
    for origin in range(32):
        hits = []
        for path, _ in paths:
            simplex = mask(v ^ origin for v in path)
            hits.append(mask(i for i, (vertices, _) in enumerate(carriers) if simplex & ~vertices == 0))
        staircase.append(tuple(hits))
    required = [0]
    cuts = [minimal_sets({project(s) for s in hits}) for hits in staircase]
    for opts in sorted(cuts, key=lambda c: -min(x.bit_count() for x in c)):
        required = minimal_sets({r | s for r in required for s in opts})
    assert set(sufficient) <= set(required)
    assert min(x.bit_count() for x in required if x not in sufficient) == 20
    small = [x for x in sufficient if x.bit_count() <= 19]
    assert Counter(x.bit_count() for x in small) == {12: 2, 15: 2, 17: 2, 18: 4}
    for x in small:
        seed, order = degree_one[x]
        colours = priority_colours(seed, order, positive)
        assignment = [next(i for i, c in enumerate(colours) if c >> v & 1) for v in range(64)]
        assert all(len({assignment[v] for v in range(64) if (v >> a & 1) == b}) < 7
                   for a in range(6) for b in range(2))
        projected = project(mask(i for i, (verts, _) in enumerate(carriers) if all(verts & c for c in colours)))
        assert projected == x
        degree = 0
        for path, sign in paths:
            names = [assignment[v ^ seed] for v in path]
            if len(set(names)) == 7:
                degree += (-1)**seed.bit_count() * sign * orientation(names)
        assert abs(degree) == 1
        print(f'{x.bit_count()} classes, seed {seed}, order {order}, degree {degree}:',
              [g[0] for i,g in enumerate(classes) if x >> i & 1])
    print(f'{len(required)} minimal staircase permissions; all minima below 20 admit unit degree.')
    survivors = []
    for i,j in combinations(range(len(classes)), 2):
        if not all(c & ((1 << i) | (1 << j)) for c in sufficient):
            continue
        protected = orbits[i] | orbits[j]
        selected = classes[i] + classes[j]
        origins = [a for a, hits in enumerate(staircase) if all(s & protected for s in hits)]
        if origins:
            print('Integral staircase on protected classes', (classes[i][0], classes[j][0]), 'at', origins[0])
            length = 720
        else:
            length = integral_nerve_certificate(selected, carriers)
        survivors.append((classes[i][0], classes[j][0], length))
    assert survivors == [(7,37,336), (13,37,720), (13,38,720), (24,38,320)]
    print('All four surviving two-class protections fill integrally:', survivors)


if __name__ == '__main__':
    solve()
