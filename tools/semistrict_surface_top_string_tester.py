"""Check top-string contraction and expansion at the signed sections of a tree."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import (arr, infer, maximal_vars, ps_boundary_vars, src, sub_from, subst_tm, subst_ty,
                  tdim_tm, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite
from semistrict_surface_positional_tags import loop_tower


def tester(rank):
    if rank == 1:
        return tree_ctx(((),))
    ctx = loop_tower(rank - 2)
    pole = v(rank - 2)
    parallel = arr(infer(ctx, pole), pole, pole)
    ctx += (parallel, parallel)
    return ctx + (arr(parallel, v(rank - 1), v(rank)),)


def row(rank, lengths):
    if rank == 1:
        length, = lengths
        return tree_ctx(((),) * length)
    tree = tuple(((),) * length for length in lengths)
    for _ in range(rank - 2):
        tree = (tree,)
    return tree_ctx(tree)


def check_map(source, target, labels):
    assert len(labels) == len(source)
    for ty, label in zip(source, labels, strict=True):
        assert infer(target, label) == subst_ty(ty, labels)


def emit_map(emitter, name, source, target, labels):
    p, q, sigma = emitter.ctx(source), emitter.ctx(target), emitter.sub(labels)
    emitter.checks.append(f'{name} : {q} ⊢sub {sigma} ∶ {p}\n'
                          f'{name} = from-just (checkSub {q} (from-just (checkCtx {q})) {sigma} {p})\n')


def check_row(rank, lengths, emitter=None):
    long = row(rank, lengths)
    short = row(rank, [min(length, 1) for length in lengths])
    test = tester(rank)
    down, up, fold = {}, {}, {}
    old = iter(maximal_vars(long))
    for slot, (length, i) in enumerate(zip(lengths, maximal_vars(short), strict=True)):
        if length:
            chain = [next(old) for _ in range(length)]
            down[chain[0]] = v(i)
            for j in chain[1:]:
                down[j] = ident(short, tgt(short, v(i)))
            up[i] = composite(long, rank - 1, [v(j) for j in chain])
            fold[i] = v(len(test) - 1)
        else:
            j = next(old)
            down[j], up[i] = v(i), v(j)
            fold[i] = v(len(test) - 3 + slot % 2)
    assert next(old, None) is None
    contract = sub_from(long, short, down)
    expand = sub_from(short, long, up)
    labels = sub_from(short, test, fold)
    for name, source, target, sigma in [('contract', long, short, contract), ('expand', short, long, expand),
                                        ('colour', short, test, labels)]:
        check_map(source, target, sigma)
        if emitter is not None:
            emit_map(emitter, name, source, target, sigma)
    for sign in ('-', '+'):
        for j in ps_boundary_vars(long, rank - 1, sign):
            assert subst_tm(contract[j], expand) == v(j)
    # Recover the entire top shape from its two labelled sections.
    for i, length in zip(maximal_vars(short), lengths, strict=True):
        cell = v(i)
        if tdim_tm(short, cell) == rank:
            ends = src(short, cell), tgt(short, cell)
        else:
            ends = cell, cell
        s, t = [subst_tm(end, labels) for end in ends]
        assert (s != t) == bool(length)
        if s != t:
            assert (s, t) == (src(test, v(len(test) - 1)), tgt(test, v(len(test) - 1)))


def check_labelled_cycle(emitter):
    rank = 5
    graph = loop_tower(rank - 2)
    pole = v(len(graph) - 1)
    parallel = arr(infer(graph, pole), pole, pole)
    a, b, c = (v(len(graph) + i) for i in range(3))
    graph += (parallel,) * 3
    ab, ba, ac, cb = (v(len(graph) + i) for i in range(4))
    graph += tuple(arr(parallel, start, end) for start, end in [(a, b), (b, a), (a, c), (c, b)])
    long, short = row(rank, (3, 3, 0)), row(rank, (1, 0, 0))
    top, idle_loop, idle = map(v, maximal_vars(short))
    original = sub_from(long, graph, dict(zip(maximal_vars(long), (ab, ba, ac, cb, ba, ac, b), strict=True)))
    contract = sub_from(long, short, dict(zip(maximal_vars(long),
                         (top, ident(short, tgt(short, top)), ident(short, tgt(short, top)),
                          ident(short, idle_loop), ident(short, idle_loop), ident(short, idle_loop), idle),
                         strict=True)))
    # The first slot takes a shorter path with the same named ends.
    # The nonempty return in the second slot becomes stationary at c.
    replay = sub_from(short, graph, dict(zip(maximal_vars(short), (ac, c, b), strict=True)))
    for name, source, target, sigma in [('oldLabels', long, graph, original),
                                        ('collapseReturn', long, short, contract),
                                        ('shortLabels', short, graph, replay)]:
        check_map(source, target, sigma)
        if emitter is not None:
            emit_map(emitter, name, source, target, sigma)
    for sign in ('-', '+'):
        for j in ps_boundary_vars(long, rank - 1, sign):
            assert subst_tm(contract[j], replay) == original[j]

    test = tester(rank)
    colour = sub_from(short, test, dict(zip(maximal_vars(short),
                          (v(len(test) - 1), v(len(test) - 3), v(len(test) - 3)), strict=True)))
    check_map(short, test, colour)
    generic = ucomp(long)
    compressed = subst_tm(generic, contract)
    replayed, tested = subst_tm(compressed, replay), subst_tm(compressed, colour)
    old_type = subst_ty(infer(long, generic), original)
    assert infer(graph, replayed) == old_type
    if emitter is not None:
        emit_map(emitter, 'testLabels', short, test, colour)
        emitter.check_typed('longPaste', long, generic)
        for name, target, term, expected, premise, assignment in [
                ('compressedPaste', short, compressed, infer(short, compressed),
                 '(snd longPaste-typed)', 'collapseReturn'),
                ('replayedPaste', graph, replayed, old_type, 'compressedPaste', 'shortLabels'),
                ('testPaste', test, tested, infer(test, tested), 'compressedPaste', 'testLabels')]:
            emitter.checks.append(f'{name} : {emitter.ctx(target)} ⊢tm {emitter.tm(term)} ∶ {emitter.ty(expected)}\n'
                                  f'{name} = substL {premise} {assignment}\n')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    cases = [(1, (i,)) for i in range(1, 5)]
    cases += [(rank, lengths) for rank in range(2, 7)
              for lengths in product(range(4), repeat=3)]
    for rank, lengths in cases:
        check_row(rank, lengths)
    emitter = Emitter() if args.agda_dir else None
    check_labelled_cycle(emitter)
    if args.agda_dir:
        check_row(5, (3, 0, 2), emitter)
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        source = emitter.module('TopStringTester', __doc__)
        (args.agda_dir / 'TopStringTester.agda').write_text(
            source.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))
    print(f'Checked {len(cases)} top-string contractions, both signed sections, their tester labels, and a positive return with repeated labels.')


if __name__ == '__main__':
    main()
