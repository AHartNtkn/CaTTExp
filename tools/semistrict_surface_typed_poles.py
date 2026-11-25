"""Verify strict factor isolation and typed rewriting at unrelated compound poles."""
import argparse
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import arr, disc_tree, infer, tree_ctx, v
from relative_coherence_hidden_seam import identity
from semistrict_surface_compound_rewriting import Serial, search
from semistrict_surface_flat_heads import check_weak
from semistrict_surface_grid_tracks import temporal
from semistrict_surface_rank_cut import RankCut
from semistrict_surface_strict_factors import Diagram, proper_factors, strict


def grid(words):
    # All horizontal arrows are f, and a,b are independent vertical endos on f.
    def column(w):
        return Diagram(1, tuple((Diagram(c, ()), 1) for c in w))
    return Diagram(0, tuple((column(w), 0) for w in words))


def grid_checks():
    strings = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb']
    diagrams = [x for n in (1, 2) for x in product(strings, repeat=n) if any(x)]
    count = 0
    for pattern, target in product(diagrams, repeat=2):
        expected = pattern != target and any(all(s in t for s, t in zip(pattern, target[k:]))
                                             for k in range(len(target) - len(pattern) + 1))
        assert (grid(pattern) in proper_factors(grid(target))) == expected
        count += 1
    return count


def examples(rank, checker):
    base = tree_ctx(disc_tree(rank-2))
    face = v(len(base)-1)
    ty = arr(infer(base, face), face, face)
    x, y = v(len(base)), v(len(base)+1)
    base += (ty, ty)
    p = temporal(base, x, y)
    q = temporal(base, temporal(base, y, x), x)
    q2 = temporal(base, y, temporal(base, x, x))
    assert strict(base, q) == strict(base, q2) and strict(base, p) != strict(base, q)
    serial = Serial(base, [(p, q), (q2, p), (q, q2)], rank)
    a, b, c = serial.names
    iq, ip = identity(base, q), identity(base, p)
    birth = serial.normal((2,), q, q)
    serial.declare(iq, birth)
    serial.declare(birth, iq)
    # Empty-to-empty histories cannot take the Q birth at P, even once.
    assert search(serial.rules, (), (), (1, 1)) is not None
    assert serial.typed_search(ip, ip, (1, 1)) is None
    cycle = serial.typed_search(iq, iq, (1, 1))
    assert cycle == [(0, 0), (1, 0)]
    query = serial.normal((0, 1), p, p)
    extra = serial.normal((0, 2, 1), p, p)
    inserted = serial.typed_search(query, extra, (1, 0))
    assert inserted == [(0, 1)]
    assert serial.typed_search(query, extra, (0, 1)) is None
    for s, t, hist in ((iq, iq, cycle), (query, extra, inserted)):
        proof = serial.replay(s, t, hist)
        if checker:
            check_weak(checker, serial.ctx, proof, arr(infer(serial.ctx, s), s, t))
    try:
        Serial(base, [(p, temporal(base, p, y))], rank)
    except ValueError as e:
        assert 'proper factor' in str(e)
    else:
        raise AssertionError('A wrapped pole passed the isolation test')
    return 2


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path)
    args = parser.parse_args()
    print(f'{grid_checks()} labelled factor tests agree with independent substring and column tests')
    with TemporaryDirectory() as tmp:
        checker = RankCut(6, args.checker.resolve(), Path(tmp)) if args.checker else None
        for rank in (2, 3, 5):
            print(f'Degree {rank+1}: {examples(rank, checker)} typed replays; empty position distinguished')
