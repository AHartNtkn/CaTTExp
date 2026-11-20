"""Check temporal reassociation on a mixed ladder and through a fixed lower whisker."""
from argparse import ArgumentParser
from functools import cache
from pathlib import Path

from catt import (arr, chain_tree, comp2, disc_tree, fv_ty, glue_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, subst_ty, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_constant_cylinder import correction as contract_identity, whisk
from gray_globe_exterior_actions import certificate, coherence
from gray_penultimate_partial_actions import data, distribute
from gray_partial_cylinder_sections import positions
from gray_temporal_partial_actions import action, rails
from gray_top_slot_promotion import expand, support, time_inclusion
from rc2 import rc2_full
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import composite, string_tree


def bracketings(ctx, cut, edges):
    a, b, c = edges
    return comp2(ctx, cut, comp2(ctx, cut, a, b), c), comp2(ctx, cut, a, comp2(ctx, cut, b, c))


def ladder():
    old = tree_ctx(chain_tree(3))
    ctx, copies, changes = data(old, frozenset(range(len(old))))
    binary = chain_tree(2)
    arity = tree_ctx(binary)
    marks = frozenset(range(len(arity)))
    square, chart, _ = action(binary, marks)
    _, ends, rails = data(arity, marks)

    @cache
    def lift(term):
        if term[0] == 'v':
            return changes[term[1]]
        assert term[1] == arity
        labels = [None]*len(chart)
        for i, arg in enumerate(term[3]):
            for e in (0, 1):
                labels[ends[e][i][1]] = subst_tm(arg, copies[e])
            labels[rails[i][1]] = lift(arg)
        return subst_tm(square, tuple(labels))

    w, z = bracketings(old, 0, map(v, maximal_vars(old)))
    p = coherence(old, w, z)
    left = comp2(ctx, 0, subst_tm(p, copies[0]), lift(tgt(old, w)))
    right = comp2(ctx, 0, lift(src(old, w)), subst_tm(p, copies[1]))
    a, b = comp2(ctx, 1, left, lift(z)), comp2(ctx, 1, lift(w), right)
    cell = rc2_full(ctx, a, b)
    assert infer(ctx, cell) == arr(infer(ctx, a), a, b)
    assert top_counts(ctx, lift(w)) == top_counts(ctx, lift(z)) and not top_counts(ctx, cell)
    print('Checked the associator on three pasted moving squares.', flush=True)


def distributor(k, j, side, emitter):
    cut = k-1
    path = string_tree(cut, [k]*3)
    inner = path
    for _ in range(j):
        inner, = inner
    joint = disc_tree(1)+inner if side else inner+disc_tree(1)
    for _ in range(j):
        joint = (joint,)
    ctx, old = tree_ctx(joint), tree_ctx(path)
    slots = list(map(v, maximal_vars(ctx)))
    rail = slots.pop(0 if side else -1)

    def pad(t):
        return whisk(ctx, j, t, rail, side)

    names = maximal_vars(old)
    lab = sub_from(old, ctx, dict(zip(names, slots, strict=True)))
    distributed = sub_from(old, ctx, dict(zip(names, map(pad, slots), strict=True)))
    w, z = bracketings(old, cut, map(v, names))
    p = coherence(old, w, z)

    def correction(t):
        if t[0] == 'v':
            return None
        l, r = (t[3][i] for i in maximal_vars(t[1]))
        a, b = (subst_tm(q, lab) for q in (l, r))
        steps = [distribute(ctx, cut, a, b, [(j, rail)], side, False)]
        hl, hr = correction(l), correction(r)
        if hl is not None:
            steps.append(comp2(ctx, cut, hl, pad(b)))
        if hr is not None:
            steps.append(comp2(ctx, cut, subst_tm(l, distributed), hr))
        cell = composite(ctx, k, steps)
        assert (src(ctx, cell), tgt(ctx, cell)) == (pad(subst_tm(t, lab)), subst_tm(t, distributed))
        return cell

    a = comp2(ctx, k, pad(subst_tm(p, lab)), correction(z))
    b = comp2(ctx, k, correction(w), subst_tm(p, distributed))
    cell = coherence(ctx, a, b)
    wanted = arr(infer(ctx, a), a, b)
    assert infer(ctx, cell) == wanted and not top_counts(ctx, cell)
    if emitter:
        certificate(emitter, ctx)('associator-distributor', cell, wanted)


def subdivision(k, emitter):
    """One top string gains subdivisions and another collapses to an identity."""
    r = k-1
    base = glue_tree(r, r-1, r)
    base_ctx = tree_ctx(base)
    names = positions(base)
    groups = dict(zip(maximal_vars(base_ctx), ((0, 2, 1), (0, 0)), strict=True))
    def expanded(sizes):
        return expand(base, {names[i][0]: n for i, n in sizes.items() if n})
    qt, (qs, _), qe = expanded({i: len(ns) for i, ns in groups.items()})
    pt, (ps, _), pe = expanded({i: sum(ns) for i, ns in groups.items()})
    q, p = tree_ctx(qt), tree_ctx(pt)

    def cylinder(chart):
        marks = {0}
        for i, ty in enumerate(chart):
            if fv_ty(ty) & marks:
                marks.add(i)
        return marks, *data(chart, frozenset(marks))

    qm, cq, qc, qh = cylinder(q)
    pm, cp, pc, ph = cylinder(p)
    labels = [None]*len(q)
    mixed = {}
    for i, j in zip(qs, ps):
        labels[i] = v(j)
    for i, widths in groups.items():
        edges = pe.get(i, [])
        offset, current = 0, v(ps[i])
        for h, width in zip(qe[i], widths, strict=True):
            if width:
                arity_tree = string_tree(r, [k]*width)
                arity = tree_ctx(arity_tree)
                part = list(map(v, edges[offset:offset+width]))
                inc = sub_from(arity, p, dict(zip(maximal_vars(arity), part, strict=True)))
                term = subst_tm(ucomp(arity), inc)
                if h in qm:
                    selected = frozenset(j for j, z in enumerate(inc) if z[1] in pm)
                    step, chart, _ = action(arity_tree, selected)
                    _, cc, ch = data(arity, selected)
                    lift = time_inclusion(chart, cc, ch, pc, ph, [z[1] for z in inc])
                    mixed[h] = subst_tm(step, lift)
            else:
                term = ident(p, current)
                if h in qm:
                    steps = [contract_identity(cp, subst_tm(current, pc[e]),
                                               [*rails(p, current, ph, e), ph[current[1]]], e, bool(e))
                             for e in (0, 1)]
                    mixed[h] = comp2(cp, k, *steps)
            labels[h] = term
            assert src(p, term) == current
            current = tgt(p, term)
            labels[tgt(q, v(h))[1]] = current
            offset += width

    lifted = [None]*len(cq)
    for i, arg in enumerate(labels):
        assert infer(p, arg) == subst_ty(q[i], labels[:i])
        assert (i in qm) == bool(support(p, arg) & pm)
        for e in (0, 1):
            lifted[qc[e][i][1]] = subst_tm(arg, pc[e])
        if i in qm:
            lifted[qh[i][1]] = mixed[i] if i in mixed else ph[arg[1]]
    for i, arg in enumerate(lifted):
        assert infer(cp, arg) == subst_ty(cq[i], lifted[:i])
    old, new = subst_tm(ucomp(q), labels), ucomp(p)
    assert infer(p, old) == infer(p, new) and top_counts(p, old) == top_counts(p, new)
    if emitter:
        g, target, sigma = emitter.ctx(cp), emitter.ctx(cq), emitter.sub(tuple(lifted))
        emitter.checks.append(
            f'subdivision : {g} ⊢sub {sigma} ∶ {target}\n'
            f'subdivision = from-just (checkSub {g} (from-just (checkCtx {g})) {sigma} {target})\n')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('rank', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.rank < 2:
        parser.error('rank must be at least two')
    out = Emitter() if args.agda else None
    ladder()
    for k in range(2, args.rank+1):
        subdivision(k, out if k == args.rank else None)
        for j in range(k-1):
            for side in (0, 1):
                distributor(k, j, side, out if (k, j, side) == (args.rank, 0, 1) else None)
        print(f'Rank {k}: checked both whiskers at each of {k-1} lower cuts and a subdivision with empty blocks.', flush=True)
    if out:
        args.agda.write_text(out.module(args.agda.stem, 'Associator and lower whisker distributor.'))
