"""Realize a signed sum of bracket boundaries by a single based bracket."""
from argparse import ArgumentParser
from collections import Counter
from pathlib import Path

from canonical_gray_cube import build_cube
from catt import STAR, arr, check_ctx, comp2, infer, subst_tm, tdim, tdim_tm, v
from emit_agda import Emitter
from relative_coherence_colour_degree import degree_test
from relative_coherence_cut import top_counts
from relative_coherence_hidden_seam import identity


class Brackets:
    """A finite part of P(V), using one generator for each literal boundary."""

    def __init__(self, vertices):
        self.ctx = (STAR,) * vertices
        self.generators = {}

    def bracket(self, source, target):
        ty = infer(self.ctx, source)
        assert infer(self.ctx, target) == ty
        pair = (source, target)
        if pair not in self.generators:
            self.generators[pair] = v(len(self.ctx))
            self.ctx += (arr(ty, source, target),)
        return self.generators[pair]

    def base_pair(self, source, target, point):
        """Whisker the two terms identically at each cut, including the last."""
        assert infer(self.ctx, source) == infer(self.ctx, target)
        degree = tdim_tm(self.ctx, source)
        pole = point
        for cut in range(degree):
            faces = infer(self.ctx, source)
            while tdim(faces) > cut:
                faces = faces[1]
            left = self.bracket(pole, faces[2])
            right = self.bracket(faces[3], pole)

            def pad(term):
                return comp2(self.ctx, cut, comp2(self.ctx, cut, left, term), right)

            source, target = pad(source), pad(target)
            faces = infer(self.ctx, source)
            assert faces == infer(self.ctx, target)
            for _ in range(degree - cut - 1):
                faces = faces[1]
            assert faces == arr(infer(self.ctx, pole), pole, pole)
            if cut + 1 < degree:
                pole = identity(self.ctx, pole)
        return source, target


def difference(ctx, source, target):
    counts = top_counts(ctx, target)
    counts.subtract(top_counts(ctx, source))
    return {g: c for g, c in counts.items() if c}


def coloured_cube():
    cube, _ = build_cube()
    p = Brackets(4)
    # This is the minimum colouring of the typed three-cube of relative degree -1.
    colours = [min([3] + [i for i in range(3) if mask >> i & 1]) for mask in range(8)]
    labels = []
    for i, ty in enumerate(cube[:-1]):
        if ty == STAR:
            labels.append(v(colours[i]))
        else:
            labels.append(p.bracket(*(subst_tm(t, labels) for t in ty[2:])))
    endpoints = tuple(subst_tm(t, labels) for t in cube[-1][2:])
    based = p.base_pair(*endpoints, v(0))
    assert difference(p.ctx, *endpoints) == difference(p.ctx, *based)
    p.bracket(*based)
    check_ctx(p.ctx)
    assert degree_test(p.ctx, list(range(4)), 3) == ({len(p.ctx) - 1: 1}, -1)
    print("Coloured three-cube: one based bracket, relative degree -1.")


def nested_pair(p, source, target, via, degree):
    direct = p.bracket(source, target)
    first = p.bracket(source, via)
    second = p.bracket(via, target)
    detour = comp2(p.ctx, 0, first, second)
    for k in range(1, degree):
        next_direct = p.bracket(direct, detour)
        loop = p.bracket(direct, direct)
        detour = comp2(p.ctx, k, loop, next_direct)
        direct = next_direct
    return direct, detour


def signed_pair(degree, agda):
    p = Brackets(7)
    left = nested_pair(p, v(1), v(2), v(3), degree)
    right = nested_pair(p, v(4), v(5), v(6), degree)
    expected = Counter(difference(p.ctx, *left))
    expected.subtract(difference(p.ctx, *right))
    first = p.base_pair(*left, v(0))
    second = p.base_pair(*reversed(right), v(0))
    source, target = [comp2(p.ctx, degree - 1, a, b) for a, b in zip(first, second)]
    ty = infer(p.ctx, source)
    assert infer(p.ctx, target) == ty
    assert difference(p.ctx, source, target) == dict(expected)
    assert set(expected.values()) == {-1, 1}
    comparison = p.bracket(source, target)
    expected_type = arr(ty, source, target)
    assert infer(p.ctx, comparison) == expected_type
    check_ctx(p.ctx)
    if degree == 5:
        assert degree_test(p.ctx, list(range(7)), 6) is None
    print(f'Rank {degree + 1}: {len(p.ctx)} declarations, signed difference {dict(expected)}.')
    if agda:
        emitter = Emitter()
        emitter.check_type('basedComparison', p.ctx, comparison, expected_type)
        agda.write_text(emitter.module(agda.stem, 'Based representative for two signed columns.'))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--term-degree', type=int, default=5)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.term_degree < 2:
        parser.error('--term-degree must be at least two for the signed test')
    coloured_cube()
    signed_pair(args.term_degree, args.agda)
