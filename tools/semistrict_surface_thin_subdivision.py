"""Check the switched unary/crossing boundaries and the marked exchange count."""
from argparse import ArgumentParser
from itertools import permutations
from pathlib import Path

from catt import (chain_tree, comp2, disc_tree, fv_tm, fv_ty, infer, maximal_vars,
                  src, subst_tm, tdim, tdim_tm, tgt, tree_ctx, v)
from ct_suspension import susp_tm
from relative_coherence_exchange_faces import composite, head
from semistrict_surface_directed_power_queries import apply, crossing, parallel_split, square
from semistrict_surface_inverse_completion import DerivationEmitter
from semistrict_surface_positional_tags import loop_tower


def marked_inputs(size, split_left):
    ctx = tree_ctx(((chain_tree(size),), disc_tree(1), disc_tree(1)))
    *moves, b, c = map(v, maximal_vars(ctx))
    f = moves[0]
    g = crossing(ctx, b, c)
    if split_left:
        wing = src(ctx, src(ctx, g))
        fixed = tgt(ctx, src(ctx, f))
    else:
        wing = tgt(ctx, tgt(ctx, g))
        fixed = src(ctx, src(ctx, f))
    changes = [comp2(ctx, 0, move, wing) for move in moves]
    moved = comp2(ctx, 0, fixed, g)
    inputs = changes + [moved] if split_left else [moved] + changes
    return ctx, inputs


def check_history_marks(size):
    # Independent atomic histories include swaps involving the updated slot.
    # Compare event tracking along each edge with the data read from its ends.
    for initial in permutations('abc'):
        for start in range(size + 1):
            pending = [(initial, start, frozenset(), 0)]
            seen = set()
            while pending:
                order, stage, marks, crosses = pending.pop()
                assert marks == frozenset(range(start + 1, stage + 1))
                assert crosses == (initial.index('b') > initial.index('c')
                                   and order.index('b') < order.index('c'))
                if (order, stage) in seen:
                    continue
                seen.add((order, stage))
                if stage < size:
                    pending.append((order, stage + 1, marks | {stage + 1}, crosses))
                for i in range(len(order) - 1):
                    left, right = order[i:i + 2]
                    if left > right:
                        swapped = order[:i] + (right, left) + order[i + 2:]
                        pending.append((swapped, stage, marks, crosses + ((left, right) == ('c', 'b'))))


def partition_route(ctx, inputs, size, cuts, split_left):
    strip, direct, _ = parallel_split(size, shift=1, split_left=split_left)
    if len(cuts) == 1:
        return apply(ctx, (strip, direct), inputs)
    tips = list(map(v, maximal_vars(strip)))
    moves, single = (tips[:-1], tips[-1]) if split_left else (tips[1:], tips[0])
    blocks = [composite(strip, 2, moves[lo:hi]) for lo, hi in zip((0, *cuts[:-1]), cuts, strict=True)]
    small, _, pieces = parallel_split(len(cuts), shift=1, split_left=split_left)
    route = apply(strip, (small, pieces), blocks + [single] if split_left else [single] + blocks)
    enter = head(strip, src(strip, direct), src(strip, route))
    leave = head(strip, tgt(strip, route), tgt(strip, direct))
    fitted = composite(strip, 3, [enter, route, leave])
    return apply(ctx, (strip, fitted), inputs)


def check_boundary(size, split_left, emitter):
    ctx, inputs = marked_inputs(size, split_left)
    *updates, b, c = maximal_vars(ctx)
    unary = set(updates)
    outer, chi = square(2)
    native = susp_tm(chi)

    def marks(term):
        if term[0] == 'v':
            return {term[1]} if term[1] in unary else set()
        _, arity, ty, labels = term
        tips = maximal_vars(arity)
        if (arity, ty) == (outer, chi[2]):
            if b in fv_tm(labels[tips[0]]) and c in fv_tm(labels[tips[1]]):
                return {'cross'}
        return set().union(*(marks(labels[i]) for i in tips if tdim_tm(ctx, labels[i]) == 3))

    def exchanges(term):
        _, arity, ty, labels = term
        tips = maximal_vars(arity)
        if (arity, ty) == (native[1], native[2]):
            return [(marks(labels[tips[0]]), marks(labels[tips[1]]))]
        return [pair for i in tips if tdim_tm(ctx, labels[i]) == 4 for pair in exchanges(labels[i])]

    def read(term):
        pairs = exchanges(term)
        return [(a & unary, 'cross' in g)
                for left, right in pairs for a, g in [(left, right) if split_left else (right, left)]]

    direct = partition_route(ctx, inputs, size, (size,), split_left)
    signatures = set()
    tower = loop_tower(3)
    fold = tuple(v(tdim(ty) + 1) for ty in ctx)
    folded_type = infer(tower, subst_tm(direct, fold))
    folded_faces = set()
    for mask in range(1 << (size - 1)):
        cuts = tuple(i for i in range(1, size) if mask & (1 << (i - 1))) + (size,)
        route = partition_route(ctx, inputs, size, cuts, split_left)
        pairs = read(route)
        actual = frozenset(frozenset(events) for events, has_cross in pairs if has_cross)
        expected = frozenset(frozenset(updates[lo:hi]) for lo, hi in zip((0, *cuts[:-1]), cuts, strict=True))
        assert actual == expected and len(pairs) == len(actual)
        assert infer(ctx, route) == infer(ctx, direct)
        assert set(fv_tm(route)) | set(fv_ty(infer(ctx, route))) == set(range(len(ctx)))
        signatures.add(actual)
        folded = subst_tm(route, fold)
        assert infer(tower, folded) == folded_type
        folded_faces.add(folded)
    assert len(folded_faces) == len(signatures) == 1 << (size - 1)
    paste = route  # The last mask cuts between every two updates.
    if emitter is None or size != 2:
        return

    side = 'left' if split_left else 'right'
    emitter.check_type(side + 'Direct', ctx, direct, infer(ctx, paste))
    emitter.check_type(side + 'Paste', ctx, paste, infer(ctx, direct))
    term_type = emitter.ty(infer(ctx, direct))
    emitter.checks.append(f'{side}SingleHead : cohCase {emitter.ctx(ctx)} {term_type} '
                          f'{emitter.tm(direct)} {emitter.tm(paste)} ≡ false\n{side}SingleHead = refl\n')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = DerivationEmitter() if args.agda_dir else None
    for size in range(2, 6):
        check_history_marks(size)
        for side in (True, False):
            check_boundary(size, side, emitter)
    if emitter:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        source = emitter.module('ThinSubdivision', __doc__).replace(
            'open import CaTTExp.Pure\n', 'open import CaTTExp.Gray.Pure\n'
            'open import CaTTExp.Pure using (∅)\n'
            'open import CaTTExp.PastingCheck ∅ using () renaming (checkPs to pastable)\n')
        (args.agda_dir / 'ThinSubdivision.agda').write_text(source)
    print('Checked 60 partition signatures at both placements in sizes 2 through 5 and their folded endpoints.')


if __name__ == '__main__':
    main()
