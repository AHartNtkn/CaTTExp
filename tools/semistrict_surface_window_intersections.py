"""Check intersections of insertion exteriors and the mixed-height balance equation."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (arr, comp2, disc_tree, infer, maximal_vars, src, sub_from, subst_tm,
                  tdim_tm, tgt, tree_ctx, v)
from catt_unit_ordered_exchange import temporal_words
from partial_cylinder_steiner import trees
from relative_coherence_exchange_faces import head
from semistrict_surface_elementary_insertions import exterior, slots, subtree
from semistrict_surface_exact_boundary import run
from semistrict_surface_insertion_cut import Assertions, variables
from semistrict_surface_moore_insertion import height
from semistrict_surface_scalar_pairs import splice
from semistrict_surface_seam_descent import drop, erase, then


def suspend(tree, times):
    for _ in range(times):
        tree = (tree,)
    return tree


@cache
def collapse(tree, parent, start, stop):
    """Return the tree with this window replaced by a disc, and its exterior."""
    row = subtree(tree, parent)
    block = row[start:stop]
    rank = height(block)
    small_row = row[:start] + (disc_tree(rank - 1),) + row[stop:]
    small = small_row
    # splice replaces a child by a list; for an internal row preserve its parent.
    if parent:
        small = splice(tree, parent, suspend((small_row,), len(parent) - 1))
    large, inc = exterior(small, parent + (start,), suspend(block, len(parent)))
    assert large == tree
    return small, inc


@cache
def retract(tree, parent, start, stop, keep):
    """Prune the window to one protected leaf, or to its lower pole for keep=None."""
    sigma = variables(tree_ctx(tree))
    while True:
        peaks = [p for p in slots(tree) if p[:len(parent)] == parent and len(p) > len(parent)
                 and start <= p[len(parent)] < stop and p != keep]
        if not peaks:
            return tree, sigma
        p = max(peaks)
        tree, q = erase(tree, p)
        sigma = then(sigma, q)
        if len(p) == len(parent) + 1:
            stop -= 1
        if keep:
            keep = drop(keep, p)


def parents(tree, path=()):
    yield path
    for i, child in enumerate(tree):
        yield from parents(child, path + (i,))


class Equations:
    def __init__(self):
        self.rice = Assertions()
        self.seen = set()
        self.counts = Counter()

    def maps(self, target, first, second, kind):
        ctx = tree_ctx(target)
        for l, r in zip(first, second, strict=True):
            if l != r and (ctx, l, r) not in self.seen:
                self.seen.add((ctx, l, r))
                self.rice.equal(ctx, l, r, kind)
        self.counts[kind] += 1


def check_windows(checks, tree):
    for p in parents(tree):
        row = subtree(tree, p)
        for a, b, c, e in combinations(range(len(row) + 1), 4):
            # First test the common refinement by the three separate blocks.
            left, ki = collapse(tree, p, a, c)
            right, kj = collapse(tree, p, b, e)
            union, ku = collapse(tree, p, a, e)
            lo, li = collapse(left, p, a, a + 1 + e - c)
            hi, lj = collapse(right, p, a, b + 1)
            assert lo == hi == union
            checks.maps(tree, then(li, ki), ku, 'union factors')
            checks.maps(tree, then(lj, kj), ku, 'union factors')

            # Common three-disc refinement, via an exterior on each side.
            x, kx = collapse(tree, p, a, b)
            xh, kh = collapse(x, p, a + 1, a + 1 + c - b)
            three, ky = collapse(xh, p, a + 2, a + 2 + e - c)
            generic = then(then(ky, kh), kx)
            for side, ext, start, stop, pair in (
                (left, ki, a + 1, a + 1 + e - c, a),
                (right, kj, a, b, a + 1),
            ):
                small, flank = collapse(side, p, start, stop)
                reduced, pair_map = collapse(three, p, pair, pair + 2)
                assert small == reduced
                checks.maps(tree, then(flank, ext), then(pair_map, generic), 'three-block factors')

            xhgt, hhgt, yhgt = (height(piece) for piece in (row[a:b], row[b:c], row[c:e]))
            if hhgt < min(xhgt, yhgt):
                # At the three-disc presentation erase the entire middle disc.
                reduced, qh = retract(three, p, a + 1, a + 2, None)
                for pair in (a, a + 1):
                    small, pair_map = collapse(three, p, pair, pair + 2)
                    assert small == reduced
                    checks.maps(small, then(pair_map, qh), variables(tree_ctx(small)),
                                'common stationary retractions')
            else:
                # Protect the overlap in a window whose maximum it attains.
                first_left = hhgt >= xhgt
                start, stop = (a, c) if first_left else (b, e)
                small, k, other, residual = (left, ki, kj, li) if first_left else (right, kj, ki, lj)
                peak = max((t for t in slots(tree) if t[:len(p)] == p and len(t) > len(p)
                            and b <= t[len(p)] < c), key=len)
                result, q = retract(tree, p, start, stop, peak)
                assert result == small
                checks.maps(small, then(k, q), variables(tree_ctx(small)), 'protected retractions')
                start, stop = (a, a + 1 + e - c) if first_left else (a, b + 1)
                peak = max((t for t in slots(small) if t[:len(p)] == p and len(t) > len(p)
                            and start <= t[len(p)] < stop), key=len)
                result, qu = retract(small, p, start, stop, peak)
                assert result == union
                route = then(other, q)
                checks.maps(small, then(then(route, qu), residual), route, 'protected image factors')


def assertions(binary, checks, flags, positive=True, allow_different_types=False):
    with TemporaryDirectory() as scratch:
        directory = Path(scratch)
        program = directory / 'Windows.catt'
        program.write_text('\n'.join(checks.commands) + '\n')
        out = run(binary, directory, program.name, flags)
        message = 'are equal' if positive else 'are not equal'
        if allow_different_types and not positive and 'do not have matching types' in out:
            assert sum(checks.count.values()) == 1 and out.count('Error: Terms') == 1, out[-2000:]
            return
        assert out.count(message) == sum(checks.count.values()) and message in out, out[-2000:]


def face_at(ctx, term, rank, face):
    while tdim_tm(ctx, term) > rank:
        term = face(ctx, term)
    return term


def face_list(ctx, cell, cut):
    rank = tdim_tm(ctx, cell)
    for degree in range(cut + 1, rank + 1):
        for sign, face in enumerate((src, tgt) if degree < rank else (src,)):
            yield degree, sign, face_at(ctx, cell, degree, face)


def check_strict_image(binary, heights, pair, kl, kr, ctx, cut):
    positive, negative = Assertions(), []
    outside = [face_list(pair, v(i), cut) for i in maximal_vars(pair)]
    left, right = map(list, outside)
    middle_rank = cut + heights[1]

    def middle(degree, sign):
        return (degree, sign) if degree < middle_rank else (middle_rank, None)

    for dl, sign_l, l in left:
        for dr, sign_r, r in right:
            term = comp2(pair, cut, l, r)
            balanced = middle(dl, sign_l) == middle(dr, sign_r)
            check = positive if balanced else Assertions()
            check.equal(ctx, subst_tm(term, kl), subst_tm(term, kr), 'signed face pair')
            if not balanced:
                negative.append(check)
                continue
            # A full head on its two actual supporting subdiscs, even when
            # both values are lower signed faces of the ambient active slots.
            if dl == dr and dl > middle_rank:
                support = tree_ctx(suspend((disc_tree(dl-cut-1),) * 2, cut))
                syms = list(map(v, maximal_vars(support)))
                a, b = temporal_words(support, *syms, cut, dl - 1)
                swap, undo = head(support, a, b), head(support, b, a)
                detour = comp2(support, dl, comp2(support, dl, swap, undo), swap)
                sigma = sub_from(support, pair, dict(zip(maximal_vars(support), (l, r), strict=True)))
                for t in (swap, head(support, swap, detour)):
                    t = subst_tm(t, sigma)
                    positive.equal(ctx, subst_tm(t, kl), subst_tm(t, kr), 'supported higher filler')
    assertions(binary, positive, ['--insertion-width', str(max(heights))])
    for check in negative:
        assertions(binary, check, ['--sua'], False, allow_different_types=True)
    return sum(positive.count.values()), len(negative)


def balance_example(binary, cut, heights):
    # heights are measured from the common parent.
    tree = suspend(tuple(disc_tree(h - 1) for h in heights), cut)
    p = (0,) * cut
    left, kl = collapse(tree, p, 0, 2)
    right, kr = collapse(tree, p, 1, 3)
    whole, ku = collapse(tree, p, 0, 3)
    assert left == right
    pair, ctx, disc = map(tree_ctx, (left, tree, whole))
    checks = check_strict_image(binary, heights, pair, kl, kr, ctx, cut)
    rank = cut + heights[1] + 1
    peaks = [face_at(pair, v(i), rank, src) for i in maximal_vars(pair)]
    orders = temporal_words(pair, *peaks, cut, rank - 1)
    positive = Assertions()
    for term in orders:
        positive.equal(ctx, subst_tm(term, kl), subst_tm(term, kr), 'sliding the middle cell')
    if heights[0] == heights[2] == heights[1] + 1:
        # Only here do the two faces use both top generators of the pair.
        swap = head(pair, *orders)
        assert infer(pair, swap) == arr(infer(pair, orders[0]), *orders)
        positive.equal(ctx, subst_tm(swap, kl), subst_tm(swap, kr), 'sliding at a full head')
    for mode in (['--insertion-width', str(max(heights))], ['--sua']):
        assertions(binary, positive, mode)
    for term in orders:
        left_term = subst_tm(term, kl)
        if heights == (2, 1, 2):
            failed = Assertions()
            failed.equal(ctx, left_term, subst_tm(term, kr), 'width-one separation')
            assertions(binary, failed, ['--insertion-width', '1'], False)
        top = v(maximal_vars(disc)[0])
        for cell in {face_at(disc, top, rank, face) for face in (src, tgt)}:
            separation = Assertions()
            separation.equal(ctx, left_term, subst_tm(cell, ku), 'union separation')
            assertions(binary, separation, ['--sua'], False)
    return checks


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--edges', type=int, default=7)
    parser.add_argument('--rice-binary', type=Path, required=True)
    args = parser.parse_args()
    binary = args.rice_binary.resolve()
    equations = Equations()
    for n in range(args.edges + 1):
        for tree in trees(n):
            check_windows(equations, tree)
    assertions(binary, equations.rice, ['--sua'])
    print(dict(equations.counts), len(equations.seen), 'distinct nonliteral equations')
    results = [balance_example(binary, cut, (2, 1, 2)) for cut in range(3)]
    for heights in ((2, 1, 3), (3, 1, 2), (3, 2, 3), (4, 2, 3)):
        results.append(balance_example(binary, 0, heights))
    print('Balanced face and filler tests:', sum(v[0] for v in results),
          'unbalanced face tests:', sum(v[1] for v in results))
    print('Layerings and swap agree across the two insertions at cuts 0, 1 and 2; '
          'both layerings separate from the union composite.')
