"""Check the punctured-simplex carriers and a typed low-dimensional star filling."""
from argparse import ArgumentParser
from collections import Counter
from functools import reduce
from itertools import product
from pathlib import Path

from catt import arr, chain_tree, check_ctx, comp2, infer, maximal_vars, sub_from, subst_tm, tree_ctx, v
from emit_agda import Emitter
from rc2 import kappa
from relative_coherence_based_columns import Brackets
from relative_coherence_cut import top_counts
from relative_coherence_face_transfer import Transfer


def carriers():
    totals, omitted = Counter(), Counter()
    for face in product('01*', repeat=5):
        if face == ('*',) * 5:
            continue
        names = set()
        for bits in product((0, 1), repeat=5):
            if all(c == '*' or int(c) == bit for c, bit in zip(face, bits)):
                names.add(min([6] + [i for i, bit in enumerate(bits, 1) if bit]))
        missing = set(range(1, 7)) - names
        assert missing
        totals[face.count('*')] += 1
        if face.count('*') == 4:
            omitted[tuple(sorted(missing))] += 1
    assert list(totals[d] for d in range(5)) == [32, 80, 80, 40, 10]
    print('242 proper faces miss a positive name; four-facet missing-name sets:', sorted(omitted.items()))


def square_filling(file):
    p = Brackets(4)
    track = Transfer(p, 3)
    def edge(x, y):
        return p.bracket(v(x), v(y))
    def pair(a, b):
        return comp2(p.ctx, 0, a, b)

    # The square's two orders of turning on coordinates send its paths to 321 and 311.
    a, b, c, loop = edge(3, 2), edge(2, 1), edge(3, 1), edge(1, 1)
    leg, r2, r1 = edge(3, 0), edge(0, 2), edge(0, 1)
    left, right = pair(a, b), pair(c, loop)
    g = p.bracket(left, right)
    plain = tree_ctx(chain_tree(3))
    x, y, z = map(v, maximal_vars(plain))
    l = comp2(plain, 0, comp2(plain, 0, x, y), z)
    r = comp2(plain, 0, x, comp2(plain, 0, y, z))

    def shuffle(args, reverse):
        sub = sub_from(plain, p.ctx, dict(zip(maximal_vars(plain), args)))
        return subst_tm(kappa(plain, r, l) if reverse else kappa(plain, l, r), sub)

    def route(reverse):
        def local(a, b):
            return p.bracket(b, a) if reverse else p.bracket(a, b)
        stages = [
            pair(local(a, pair(leg, r2)), b),
            shuffle((leg, r2, b), reverse),
            pair(leg, local(pair(r2, b), r1)),
            pair(leg, local(r1, pair(r1, loop))),
            shuffle((leg, r1, loop), not reverse),
            pair(local(pair(leg, r1), c), loop),
        ]
        if reverse:
            stages.reverse()
        return reduce(lambda a, b: comp2(p.ctx, 1, a, b), stages)

    emitter = Emitter()
    for backward, name in ((False, 'forward'), (True, 'backward')):
        seed = p.bracket(right, left) if backward else g
        via = route(backward)
        expected = infer(p.ctx, seed)
        assert infer(p.ctx, via) == expected
        assert all(not {1, 2, 3} <= track.names(i) for i in top_counts(p.ctx, via))
        certificate = p.bracket(via, seed)
        assert infer(p.ctx, certificate) == arr(expected, via, seed)
        assert abs(track.image(certificate[1])[(0, 1, 2, 3)]) == 1
        polarized = track.project({certificate[1]: 1}, 0, range(1, 4), 0)
        assert track.boundary(polarized, 0) == track.project({seed[1]: 1}, 0, range(1, 4), 0)
        if file:
            emitter.check_type(name, p.ctx, via, expected)
    check_ctx(p.ctx)
    if file:
        file.write_text(emitter.module(file.stem, 'Both punctured-simplex fillings of the coloured square.'))
    print('Both literal square fillings give unit-degree three-brackets with the prescribed polarized boundary.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    carriers()
    square_filling(args.agda)
