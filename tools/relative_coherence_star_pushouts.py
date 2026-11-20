"""Check the binary star pushouts and the alternating degree of their cubical test."""
from argparse import ArgumentParser
from collections import Counter
from functools import reduce
from pathlib import Path
from itertools import permutations

from catt import STAR, arr, check_ctx, comp2, fv_ty, infer, tdim, v
from emit_agda import Emitter
from relative_coherence_based_columns import Brackets
from relative_coherence_hidden_seam import identity
from relative_coherence_polarized_cube import vertex_names
from relative_coherence_simplex_carrier import flags, orientation


def pushouts():
    # Bits 1,...,6 index positive names; bit 0 is the common cone vertex.
    positives = 0b1111110
    supports = set(range(1, 128))
    families = {u: {s for s in supports if u & ~s}
                for u in range(2, 128, 2)}
    counts = Counter()
    for u, union in families.items():
        if u.bit_count() < 2:
            continue
        for j in range(1, 7):
            if not u & (1 << j):
                continue
            old = families[u ^ (1 << j)]
            simplex = {s for s in supports if not s & (1 << j)}
            overlap = {s for s in simplex if (u ^ (1 << j)) & ~s}
            assert old | simplex == union and old & simplex == overlap
            assert 1 in overlap and all((s | 1) in overlap for s in overlap)
            counts[u.bit_count()] += 1
    assert set(families[positives]) == {s for s in supports if s & positives != positives}
    assert [counts[k] for k in range(2, 7)] == [30, 60, 60, 30, 6]
    print('127 nonempty supports in every pushout; labelled squares by stage:', dict(sorted(counts.items())))


def alternating_degree():
    # Orient the cube by its initial mapped degree. Its sole nondegenerate
    # staircase simplex visits all six positive names in decreasing order.
    names = vertex_names(6, range(1, 6))
    paths = [(tuple(names[i] for i in path), sign) for path, sign in flags(range(5))]
    surviving = [(row, sign) for row, sign in paths if len(set(row)) == 6]
    assert len(paths) == 120 and len(surviving) == 1
    base = sum(sign * orientation(row) for row, sign in surviving)
    total = 0
    for perm in permutations(range(1, 7)):
        degree = sum(sign * orientation(tuple(perm[i - 1] for i in row))
                     for row, sign in surviving)
        assert degree == base * orientation(perm)
        total += base * orientation(perm) * degree
    assert total == 720
    print('120 staircase simplices; all 720 relabellings give the sign character and alternating value 720.')


def completed_intersections(file):
    emitter = Emitter()
    for stage in range(3, 7):
        p = Brackets(7)
        old = set(range(1, stage))
        edges = []
        for i in sorted(old):
            edges.extend((p.bracket(v(0), v(i)), p.bracket(v(i), v(0))))
        word = reduce(lambda a, b: comp2(p.ctx, 0, a, b), edges)
        three = identity(p.ctx, identity(p.ctx, word))
        excluded = p.bracket(three, three)
        four = identity(p.ctx, three)
        twice = comp2(p.ctx, 3, four, four)
        forward, backward = p.bracket(four, twice), p.bracket(twice, four)
        higher = p.bracket(forward, forward)
        outside = p.bracket(excluded, excluded)
        check_ctx(p.ctx)
        names, overlap, completed = [], [], []
        for i, ty in enumerate(p.ctx):
            deps = fv_ty(ty)
            support = {i} if ty == STAR else set().union(*(names[j] for j in deps))
            names.append(support)
            in_facet = stage not in support
            overlap.append(in_facet and not old <= support)
            completed.append(overlap[-1] or
                             (in_facet and tdim(ty) + 1 >= 5 and all(completed[j] for j in deps)))
        assert not completed[excluded[1]] and not completed[outside[1]]
        for arrow in (forward, backward, higher):
            assert not overlap[arrow[1]] and completed[arrow[1]]
        for name, q, s, t in (('forward', forward, four, twice),
                               ('reverse', backward, twice, four)):
            ty = arr(infer(p.ctx, s), s, t)
            assert infer(p.ctx, q) == ty
            if file:
                emitter.check_type(name + str(stage), p.ctx, q, ty)
    if file:
        file.write_text(emitter.module(file.stem, 'High brackets in the four-skeleton-preserving intersections.'))
    print('Stages 3 through 6: four typed opposite pairs, their six-loops, and two exclusion controls per stage.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    pushouts()
    alternating_degree()
    completed_intersections(args.agda)
