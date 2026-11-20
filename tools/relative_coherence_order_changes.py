"""Verify mixed-column enlargement and the two distributions of a pair of events."""

from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import (STAR, arr, chain_tree, check_ctx, comp2, disc_tree, fv_tm, infer,
                  maximal_vars, src, sub_from, subst_tm, tdim_tm, tgt, tree_ctx, v)
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_chart_paths import two_triangles, unitor
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity


def lanes(rank, heights):
    # Each entry is the number of (rank+1)-steps over one rank-cell.
    branches = tuple((chain_tree(n),) if n else disc_tree(1) for n in heights)
    for _ in range(rank - 2):
        branches = (branches,)
    return tree_ctx(branches)


def at(arity, ctx, values):
    slots = maximal_vars(arity)
    assert len(slots) == len(values)
    return sub_from(arity, ctx, dict(zip(slots, values)))


def order(ctx, term, atoms):
    if term in atoms:
        return (atoms.index(term),)
    if term[0] == 'v':
        return ()
    return tuple(i for entry in term[3] if tdim_tm(ctx, entry) == tdim_tm(ctx, term)
                 for i in order(ctx, entry, atoms))


def orders(ctx, left, right, rank):
    cut = rank - 2
    return (comp2(ctx, rank - 1, comp2(ctx, cut, left, src(ctx, right)),
                  comp2(ctx, cut, tgt(ctx, left), right)),
            comp2(ctx, rank - 1, comp2(ctx, cut, src(ctx, left), right),
                  comp2(ctx, cut, left, tgt(ctx, right))))


def mixed_columns(ctx, atoms, rank, emitter):
    cut = rank - 2
    pair = lanes(rank, [1, 1])
    l, r = map(v, maximal_vars(pair))
    start = orders(pair, src(pair, l), src(pair, r), rank)[0]
    end = orders(pair, tgt(pair, l), tgt(pair, r), rank)[1]
    letter = head(pair, start, end)
    whole = lanes(rank, [1, 1, 0])
    left, right, stationary = map(v, maximal_vars(whole))
    part = subst_tm(letter, at(pair, whole, [left, right]))
    enlarged = comp2(whole, cut, part, stationary)
    direct = head(whole, src(whole, enlarged), tgt(whole, enlarged))
    equality = head(whole, enlarged, direct)

    longer = lanes(rank, [2, 2, 0])
    l0, l1, r0, r1, fixed = map(v, maximal_vars(longer))
    cols = [[unitor(ctx, atom)] for atom in atoms]
    for col in cols:
        col.append(unitor(ctx, tgt(ctx, col[0])))
    last_pole = tgt(ctx, tgt(ctx, atoms[1]))
    idle = identity(ctx, identity(ctx, last_pole))
    evaluate = at(longer, ctx, cols[0] + cols[1] + [idle])
    for i, j in product(range(2), repeat=2):
        pick = at(whole, longer, [(l0, l1)[i], (r0, r1)[j], fixed])
        def read(t):
            return subst_tm(subst_tm(t, pick), evaluate)
        edge, extended, full, cell = map(read, (part, enlarged, direct, equality))
        def marked(t):
            return all(a[1] in fv_tm(t) for a in atoms)
        assert marked(edge) and not any(map(marked, edge[3]))
        assert [t for t in extended[3] if marked(t) and tdim_tm(ctx, t) == rank + 1] == [edge]
        assert order(ctx, src(ctx, extended), atoms) == (0, 1)
        assert order(ctx, tgt(ctx, extended), atoms) == (1, 0)
        expected = arr(infer(ctx, extended), extended, full)
        assert extended != full and infer(ctx, cell) == expected
        if i != j:
            name = f'mixed-{rank}-{i}-{j}'
            emitter.check_typed(name, ctx, cell)
            emitter.check_type(name, ctx, cell, expected)


def shared_slot(ctx, atoms, wire, rank, emitter):
    # Both events are now in the left slot, whose support omits the extra wire.
    cut = rank - 2
    pair = lanes(rank, [0, 0])
    x, y = map(v, maximal_vars(pair))
    ab, ba = orders(pair, x, y, rank)
    forward, back = head(pair, ab, ba), head(pair, ba, ab)
    loop = comp2(pair, rank, forward, back)
    filler = head(pair, loop, identity(pair, ab))
    label = at(pair, ctx, atoms)
    go, ret, witness = (comp2(ctx, cut, subst_tm(t, label), wire)
                        for t in (forward, back, filler))
    assert order(ctx, src(ctx, go), atoms) == order(ctx, tgt(ctx, ret), atoms) == (0, 1)
    assert order(ctx, tgt(ctx, go), atoms) == order(ctx, src(ctx, ret), atoms) == (1, 0)
    expected = arr(infer(ctx, src(ctx, witness)),
                   comp2(ctx, cut, subst_tm(loop, label), wire),
                   comp2(ctx, cut, subst_tm(identity(pair, ab), label), wire))
    assert infer(ctx, witness) == expected
    emitter.check_typed(f'shared-{rank}', ctx, witness)
    emitter.check_type(f'shared-{rank}', ctx, witness, expected)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    ctx, atoms = two_triangles()
    endpoint = v(len(ctx))
    wire = v(len(ctx) + 1)
    ctx += (STAR, arr(STAR, tgt(ctx, tgt(ctx, atoms[1])), endpoint))
    check_ctx(ctx)
    for rank in (2, 3, 4):
        mixed_columns(ctx, atoms, rank, emitter)
        shared_slot(ctx, atoms, wire, rank, emitter)
        ctx, atoms, wire = susp_ctx(ctx), [susp_tm(a) for a in atoms], susp_tm(wire)
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Order changes in a common frame.'))
    print('12 enlarged letters and 3 shared-slot contractions checked')
