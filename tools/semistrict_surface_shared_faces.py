"""Exercise simultaneous raw-head fitting and its common parameter arities."""

import argparse
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, chain_tree, coh_between, disc_tree, infer, maximal_vars,
                  sub_from, subst_tm, tgt, tree_ctx, v)
from relative_coherence_hidden_seam import identity
from semistrict_surface_flat_heads import check_weak
from semistrict_surface_grid_tracks import row_track, suspend, temporal
from semistrict_surface_insertion_cut import variables
from semistrict_surface_rank_cut import RankCut
from semistrict_surface_two_heads import common_preimages, shared_components, shared_heads


def bracketings(ctx, letters):
    if len(letters) == 1:
        yield letters[0]
    for split in range(1, len(letters)):
        for x, y in product(bracketings(ctx, letters[:split]), bracketings(ctx, letters[split:])):
            yield temporal(ctx, x, y)


def incompatible_family(rank, size, checker):
    base = tree_ctx(disc_tree(rank - 1))
    point = v(len(base) - 1)
    ty = arr(infer(base, point), point, point)
    ctx = base + (ty,) * (size + 1)
    letter = v(len(base))
    origins = [v(len(base) + 1 + i) for i in range(size)]
    # Four letters already give five inequivalent literal bracketings.
    length = 2
    while True:
        candidates = list(bracketings(ctx, (letter,) * length))
        if len(candidates) >= size:
            break
        length += 1
    words = candidates[:size]
    edges = {(i, j): v(len(ctx) + k) for k, (i, j) in enumerate(
        (i, j) for i in range(size) for j in range(size) if i != j)}
    ctx += tuple(arr(ty, origins[i], words[j]) for i, j in edges)
    alphabet = tuple(edges.values())
    ports = [(z, False) for z in origins]
    assert shared_heads(ctx, ports, alphabet) is None
    for omitted in range(size):
        smaller = [port for i, port in enumerate(ports) if i != omitted]
        counts = tuple(int(j == omitted) for i, j in edges)
        fit = shared_heads(ctx, smaller, alphabet, counts)
        assert fit and len({tgt(ctx, head) for head in fit}) == 1
        if checker:
            for head in fit:
                check_weak(checker, ctx, head, infer(ctx, head))

    for i in range(size):
        j = (i + 1) % size
        def ends(p, *xs):
            generic = list(bracketings(p, xs))
            return generic[j], generic[0]
        bridge = row_track(ctx, rank, [letter] * length, ends)
        result = temporal(ctx, edges[i, j], bridge)
        assert infer(ctx, result) == arr(ty, origins[i], words[0])
        if checker:
            check_weak(checker, ctx, result, infer(ctx, result))
            assert checker.published_equal(ctx, result, edges[i, j])
    return length


def folded_component(rank, checker):
    disc = disc_tree(rank)
    row = suspend(chain_tree(2), rank - 1)
    s, t = tree_ctx(disc), tree_ctx(row)
    top = v(maximal_vars(s)[0])
    pair = temporal(t, *(v(i) for i in maximal_vars(t)))
    alpha = sub_from(s, t, {top[1]: pair})
    beta = variables(t)
    sections = [(disc, alpha, infer(s, top)), (row, beta, infer(t, pair)),
                (disc, alpha, infer(s, top))]
    for shape, mus, h in shared_components(sections):
        lifts = list(common_preimages(shape, mus, (top, pair, top)))
        if not lifts:
            continue
        x = lifts[0]
        padded = temporal(shape, x, identity(shape, tgt(shape, x)))
        assert infer(shape, x) == infer(shape, h) == infer(shape, padded)
        images = [subst_tm(padded, mu) for mu in mus]
        assert padded in common_preimages(shape, mus, images)
        assert not list(common_preimages(shape, mus, (top, images[1], top)))
        def compare(a, b):
            return coh_between(shape, disc, [x], a, b)
        forward, back = compare(x, padded), compare(padded, x)
        roundtrip = temporal(shape, forward, back)
        six = compare(roundtrip, identity(shape, x))
        for term in (forward, back, six):
            actuals = [subst_tm(subst_tm(term, mu), sigma) for mu, (_, sigma, _) in zip(mus, sections)]
            assert len(set(actuals)) == 1
            if checker:
                check_weak(checker, t, actuals[0], infer(t, actuals[0]))
        return
    raise AssertionError('No component carrying the folded disc and the temporal row')


def word_budgets():
    ty = arr(STAR, v(0), v(0))
    a, b = v(1), v(2)
    ctx = (STAR, ty, ty, arr(ty, a, b), arr(ty, b, a))
    labels = (v(3), v(4))
    checked = 0
    for length in (1, 2):
        words = list(product((a, b), repeat=length))
        for triple in product(words, repeat=3):
            ports = [(w[0] if length == 1 else temporal(ctx, *w), j == 1)
                     for j, w in enumerate(triple)]
            minima = []
            for middle in words:
                moves = [pair for j, w in enumerate(triple)
                         for pair in (zip(middle, w) if j == 1 else zip(w, middle))]
                minima.append((moves.count((a, b)), moves.count((b, a))))
            for f, back in product(range(3), repeat=2):
                expect = any(f - i == back - j >= 0 for i, j in minima)
                assert (shared_heads(ctx, ports, labels, (f, back)) is not None) == expect
                checked += 1
    return checked


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checker', type=Path)
    args = parser.parse_args()
    with TemporaryDirectory() as scratch:
        checker = RankCut(6, args.checker.resolve(), Path(scratch))
        folded_component(4, checker)
        print('Folded 4-disc and temporal row share both 5-tracks and their 6-comparison', flush=True)
        for rank, size in ((1, 3), (5, 3), (5, 4)):
            length = incompatible_family(rank, size, checker)
            print(f'Degree {rank + 1}, {size} ports, {length} letters: exactly the proper subsets fit; '
                  'all marked two-stage repairs checked', flush=True)
        print(f'{word_budgets()} mixed-direction joint budgets agree with the word criterion', flush=True)
