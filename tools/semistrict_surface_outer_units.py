"""Check outer-unit readings and their raw representatives at compound faces."""
from argparse import ArgumentParser
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from pathlib import Path

from catt import (STAR, arr, chain_tree, coh_between, comp2, disc_tree, glue_tree, infer,
                  maximal_vars, src, sub_from, subst_tm, tdim, tree_ctx, ucomp, v)
from catt_unit_ordered_exchange import temporal_words
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity


@lru_cache(None)
def readings(word):
    """Enumerate the readings of all bracketings; None denotes the empty input."""
    if len(word) == 1:
        return {word[0]}
    result = set()
    for i in range(1, len(word)):
        for a, b in product(readings(word[:i]), readings(word[i:])):
            if a is None or b is None:
                result.add(b if a is None else a)
            else:
                result.add((a, b))
    return result


def rank_one_tests():
    checks = 0
    for width in range(1, 9):
        for word in product((None, 'f', 'g'), repeat=width):
            positive = tuple(a for a in word if a is not None)
            expected = readings(positive) if positive else {None}
            assert readings(word) == expected
            if len(positive) <= 2:
                assert len(expected) == 1
            elif len(positive) == 3:
                assert len(expected) == 2
            checks += 1
    return checks


@dataclass(frozen=True)
class Cell:
    start: int
    end: int
    rank: int
    events: str = ''

    def raise_to(self, rank):
        assert self.rank <= rank
        return Cell(self.start, self.end, rank, self.events)


def spatial(a, b):
    assert a.end == b.start
    if a.start != a.end:
        return a.raise_to(max(a.rank, b.rank))
    return b.raise_to(max(a.rank, b.rank))


def single_column_tests():
    cells = [Cell(i, i, rank) for i, rank in product((0, 1), range(1, 5))]
    cells += [Cell(0, 1, rank, word) for rank in range(1, 5)
              for word in (('',) if rank == 1 else ('', 'p', 'q', 'pq', 'qp'))]
    checks = 0
    for a, b, c in product(cells, repeat=3):
        if a.end == b.start and b.end == c.start:
            assert spatial(spatial(a, b), c) == spatial(a, spatial(b, c))
            checks += 1
    for a, b in product(cells, repeat=2):
        if a.end == b.start:
            rank = max(a.rank, b.rank) + 1
            assert spatial(a, b).raise_to(rank) == spatial(a.raise_to(rank), b.raise_to(rank))
    assert spatial(Cell(0, 0, 4), Cell(0, 1, 2, 'pq')) != spatial(Cell(0, 1, 2, 'qp'), Cell(1, 1, 4))
    return checks


def word_only_weight(ctx, term, variables):
    """The two-cell reading of the word-only model used for the head test."""
    assert tdim(infer(ctx, term)) + 1 == 2
    if term[0] == 'v':
        return variables[term[1]]
    _, arity, ty, labels = term
    if arity == tree_ctx(chain_tree(3)):
        return 1
    primitive = ucomp(arity)
    if primitive[0] != 'coh' or primitive[2] != ty:
        return 0
    return sum(word_only_weight(ctx, labels[i], variables) for i in maximal_vars(arity)
               if tdim(arity[i]) + 1 == 2) % 2


def raw_checks(emitter):
    # Specialize the three-arrow associator at a genuine missing middle column.
    line = chain_tree(2)
    ctx = tree_ctx(line)
    f, g = map(v, maximal_vars(ctx))
    unit = identity(ctx, src(ctx, g))
    plain = comp2(ctx, 0, f, g)
    a, b = comp2(ctx, 0, comp2(ctx, 0, f, unit), g), comp2(ctx, 0, f, comp2(ctx, 0, unit, g))
    three = chain_tree(3)
    tctx = tree_ctx(three)
    x, y, z = map(v, maximal_vars(tctx))
    assoc = coh_between(ctx, three, [f, unit, g],
                        comp2(tctx, 0, comp2(tctx, 0, x, y), z),
                        comp2(tctx, 0, x, comp2(tctx, 0, y, z)))
    enter = coh_between(ctx, line, [f, g], plain, a)
    leave = coh_between(ctx, line, [f, g], b, plain)
    fitted = comp2(ctx, 1, comp2(ctx, 1, enter, assoc), leave)
    ident = identity(ctx, plain)
    comparison = coh_between(ctx, line, [f, g], fitted, ident)
    reverse = coh_between(ctx, line, [f, g], ident, fitted)
    def check(name, ctx, term, s, t):
        ty = arr(infer(ctx, s), s, t)
        assert infer(ctx, term) == ty
        if emitter:
            emitter.check_type(name, ctx, term, ty)
    check('middleAssociator', ctx, fitted, plain, plain)
    check('unitReading', ctx, comparison, fitted, ident)
    check('oppositeReading', ctx, reverse, ident, fitted)

    # Instantiate the template on a one-object computad, with two-column gates
    # and a 3-generator attached at their composite. Compose at its exact end.
    base = (STAR, arr(STAR, v(0), v(0)), arr(STAR, v(0), v(0)))
    f0, g0 = v(1), v(2)
    fg, gf = comp2(base, 0, f0, g0), comp2(base, 0, g0, f0)
    base += (arr(infer(base, fg), fg, gf), arr(infer(base, gf), gf, fg))
    pasted = comp2(base, 1, v(3), v(4))
    idfg = identity(base, fg)
    base += (arr(infer(base, pasted), pasted, idfg),)
    labels = sub_from(ctx, base, dict(zip(maximal_vars(ctx), [f0, g0])))
    r, s = subst_tm(reverse, labels), subst_tm(comparison, labels)
    word = comp2(base, 2, comp2(base, 2, v(5), r), s)
    check('compoundAttachment', base, word, pasted, idfg)

    # A silent higher operand promotes the positive reading to the output rank.
    # An outer whisker and the promoted identity have raw-different 1-faces.
    # The line correction must be made before asking for a comparison.
    one = disc_tree(1)
    c = tree_ctx(one)
    edge = v(maximal_vars(c)[0])
    point = identity(c, src(c, edge))
    tower = identity(c, point)
    carried = comp2(c, 0, tower, edge)
    wing = comp2(c, 0, point, edge)
    up = coh_between(c, one, [edge], edge, wing)
    down = coh_between(c, one, [edge], wing, edge)
    corrected = comp2(c, 1, comp2(c, 1, up, carried), down)
    promoted = identity(c, edge)
    check('promotedReading', c, coh_between(c, one, [edge], corrected, promoted), corrected, promoted)

    square = tree_ctx(glue_tree(2, 0, 2))
    slots = maximal_vars(square)
    early, late = temporal_words(square, v(slots[0]), v(slots[1]), 0, 1)
    original = head(square, late, early)
    for weights in product(range(2), repeat=2):
        assignment = dict(zip(slots, weights))
        expected = sum(weights) % 2
        assert word_only_weight(square, late, assignment) == word_only_weight(square, early, assignment) == expected
    loop = (STAR, arr(STAR, v(0), v(0)))
    loop += (arr(infer(loop, v(1)), v(1), v(1)),)
    diagonal = sub_from(square, loop, {i: v(2) for i in slots})
    crossed = subst_tm(original, diagonal)
    loop += (arr(infer(loop, crossed), crossed, crossed),)
    check('squareAttachment', loop, comp2(loop, 3, v(3), v(3)), crossed, crossed)

    lhs = comp2(tctx, 0, comp2(tctx, 0, x, y), z)
    rhs = comp2(tctx, 0, x, comp2(tctx, 0, y, z))
    left_diagonal, associated = head(tctx, lhs, lhs), head(tctx, lhs, rhs)
    check('protectedDiagonal', tctx, left_diagonal, lhs, lhs)
    check('genericAssociator', tctx, associated, lhs, rhs)
    assert word_only_weight(tctx, left_diagonal, {}) == word_only_weight(tctx, associated, {}) == 1
    assert word_only_weight(tctx, identity(tctx, lhs), {}) == 0


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    print(f'{rank_one_tests()} padded words checked over every bracketing.')
    print(f'{single_column_tests()} typed spatial associations checked through rank four.')
    emitter = Emitter() if args.agda_dir else None
    raw_checks(emitter)
    print('Checked eight raw judgments and the two-cell readings of the diagonal, associator, and interchange words.')
    if emitter:
        name = 'OuterUnitReadings'
        source = emitter.module(name, __doc__).replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure')
        (args.agda_dir / (name + '.agda')).write_text(source)
