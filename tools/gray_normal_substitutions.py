"""Realize splitting and degeneracy factorizations with literal lower CaTT labels."""
from argparse import ArgumentParser
from collections import Counter
from pathlib import Path

from catt import (arr, comp2, disc_tree, infer, maximal_vars, src, sub_from, subst_tm, subst_ty,
                  tdim_tm, tgt, tree_ctx, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_exterior_actions import certificate, coherence
from gray_partial_cylinder_sections import positions
from gray_spatial_units import compare, scope_checks
from gray_thin_substitution import flat
from gray_top_slot_promotion import expand, top_action
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import composite, string_tree


class Strings:
    def __init__(self, tree, lengths):
        self.base = tree_ctx(tree)
        self.slots = maximal_vars(self.base)
        addresses = positions(tree)
        wide, (start, _), edges = expand(tree, {addresses[i][0]: n for i, n in zip(self.slots, lengths, strict=True) if n})
        self.ctx = tree_ctx(wide)
        self.start = tuple(map(v, start))
        self.rows = [list(map(v, edges.get(i, ()))) for i in self.slots]

    def section(self, offsets):
        result = list(self.start)
        for i, row, off in zip(self.slots, self.rows, offsets, strict=True):
            if off:
                result[i] = tgt(self.ctx, row[off-1])
        return tuple(result)


def blocks(tree, sizes, rank):
    """The variable-lower substitution for one list of block sizes per string."""
    q = Strings(tree, list(map(len, sizes)))
    p = Strings(tree, list(map(sum, sizes)))
    labels = dict(zip((x[1] for x in q.start), p.start, strict=True))
    for slot, old, new, ns in zip(p.slots, q.rows, p.rows, sizes, strict=True):
        point = p.start[slot]
        offset = 0
        for edge, n in zip(old, ns, strict=True):
            if n:
                letters = new[offset:offset+n]
                value = flat(p.ctx, composite(p.ctx, rank-1, letters))
                point = tgt(p.ctx, letters[-1])
            else:
                value = ident(p.ctx, point)
            labels[edge[1]] = value
            offset += n
    return q, p, sub_from(q.ctx, p.ctx, labels)


def normalized(q, p, sigma, r):
    result = tuple(flat(p, a) if tdim_tm(q, v(i)) == r else a for i, a in enumerate(sigma))
    for i, a in enumerate(result):
        assert infer(p, a) == subst_ty(q[i], result[:i])
    return result


def compose(q, p, f, g, r):
    return normalized(q, p, tuple(subst_tm(x, g) for x in f), r)


def realize(tree, t, groups, poles):
    """Label each source arrow using its ordered events and its two chosen lower writings."""
    q = Strings(tree, list(map(len, groups)))
    count = Counter(i for row in groups for part in row for i in part)
    p = Strings(tree, [count[i] for i in range(len(q.slots))])
    labels = {}
    for slot, row, parts, words in zip(q.slots, q.rows, groups, poles, strict=True):
        assert len(words) == len(parts)+1
        offsets = [0]*len(q.slots)
        labels[q.start[slot][1]] = subst_tm(words[0], p.start)
        for edge, events, a, b in zip(row, parts, words[:-1], words[1:], strict=True):
            before = p.section(offsets)
            steps = {}
            for i, n in Counter(events).items():
                sl = p.rows[i][offsets[i]:offsets[i]+n]
                steps[p.slots[i]] = flat(p.ctx, composite(p.ctx, t, sl))
                offsets[i] += n
            after = p.section(offsets)
            change = top_action(p.base, p.ctx, b, (before, after), steps)
            if change is None:
                assert not events
                change = ident(p.ctx, subst_tm(b, before))
            first = subst_tm(compare(p.base, a, b), before)
            cell = flat(p.ctx, comp2(p.ctx, t, first, change))
            assert (src(p.ctx, cell), tgt(p.ctx, cell)) == (subst_tm(a, before), subst_tm(b, after))
            assert sum(top_counts(p.ctx, cell).values()) == len(events)
            labels[edge[1]] = cell
    return q, p, sub_from(q.ctx, p.ctx, labels)


def elementary_blocks(tree, sizes, r):
    """Build the same map by elementary splits or by individual collapses."""
    q, p, direct = blocks(tree, sizes, r)
    groups = [[1]*len(row) for row in sizes]
    result = tuple(map(v, range(len(q.ctx))))
    current = q
    for i, row in enumerate(sizes):
        for j, n in enumerate(row):
            while groups[i][j] != n:
                step = [[1]*len(edges) for edges in current.rows]
                offset = sum(groups[i][:j])
                if n:
                    step[i][offset] = 2
                    groups[i][j] += 1
                else:
                    step[i][offset] = 0
                    groups[i][j] = 0
                previous, following, sigma = blocks(tree, step, r)
                assert previous.ctx == current.ctx
                current = following
                result = compose(q.ctx, current.ctx, result, sigma, r)
    assert current.ctx == p.ctx and result == direct
    return direct


def example(r, reverse, emitter):
    t = r-1
    tree = string_tree(t-1, [t]*3)
    base = tree_ctx(tree)
    a, b, c = map(v, maximal_vars(base))
    # The middle source slot lives one dimension below the other two.
    words = [comp2(base, t-1, a, b), ident(base, tgt(base, b)), c]
    groups = [[(0, 0, 1), (), (1,), ()], [()], [(), (2, 2)]]
    if reverse:
        groups[0][0] = tuple(reversed(groups[0][0]))
    poles = []
    for w, row in zip(words, groups, strict=True):
        pos = [w]
        for _ in row:
            pos.append(comp2(base, t-1, ident(base, src(base, w)), pos[-1]))
        poles.append(pos)
    q, p, tau = realize(tree, t, groups, poles)
    split_sizes = [[max(1, len(part)) for part in row] for row in groups]
    splits = elementary_blocks(tree, split_sizes, r)

    parts, new_poles = [], []
    for row, bounds in zip(groups, poles, strict=True):
        events, positions_ = [], [bounds[0]]
        for part, lo, hi in zip(row, bounds[:-1], bounds[1:], strict=True):
            events.extend([(x,) for x in part] or [()])
            positions_.extend([lo]*max(0, len(part)-1))
            positions_.append(hi)
        parts.append(events)
        new_poles.append(positions_)
    middle, same, thin = realize(tree, t, parts, new_poles)
    assert same.ctx == p.ctx and compose(q.ctx, p.ctx, splits, thin, r) == tau

    widened = []
    keep = [[] for _ in words]
    for i, row in enumerate(parts):
        newrow = []
        for part in row:
            if part:
                keep[part[0]].append(1)
                newrow.append(part)
            elif i == 1:
                newrow.append(())
            else:
                dummy = (1 if reverse else 0) if i == 0 else 2
                keep[dummy].append(0)
                newrow.append((dummy,))
        widened.append(newrow)
    same, wide, singleton = realize(tree, t, widened, new_poles)
    assert same.ctx == middle.ctx
    single_counts = [top_counts(wide.ctx, singleton[x[1]]) for row in middle.rows for x in row]
    assert all(sum(c.values()) <= 1 for c in single_counts)
    assert sum(single_counts, Counter()) == Counter(x[1] for row in wide.rows for x in row)
    assert sum(not c for c in single_counts) == 1
    collapse = elementary_blocks(tree, keep, r)
    assert compose(middle.ctx, p.ctx, singleton, collapse, r) == thin
    first = compose(q.ctx, wide.ctx, splits, singleton, r)
    assert compose(q.ctx, p.ctx, first, collapse, r) == tau
    raw = tuple(subst_tm(x, collapse) for x in first)
    changed = [i for i, (x, y) in enumerate(zip(raw, tau)) if x != y]
    assert changed and all(tdim_tm(q.ctx, v(i)) == r for i in changed)
    if emitter:
        start = len(emitter.checks)
        for name, source, target, sub in (('split', q, middle, splits), ('singleton', middle, wide, singleton),
                                           ('collapse', wide, p, collapse), ('raw-composite', q, p, raw)):
            a, b_, s = emitter.ctx(source.ctx), emitter.ctx(target.ctx), emitter.sub(sub)
            emitter.checks.append(f'{name} : {b_} ⊢sub {s} ∶ {a}\n'
                                  f'{name} = from-just (checkSub {b_} (from-just (checkCtx {b_})) {s} {a})\n')
        scope_checks(emitter, start, 'Substitutions')
        i = changed[0]
        start = len(emitter.checks)
        alpha = compare(p.ctx, raw[i], tau[i])
        certificate(emitter, p.ctx)('restore-top', alpha, arr(infer(p.ctx, raw[i]), raw[i], tau[i]))
        scope_checks(emitter, start, 'Comparison')
    return len(changed)


def unary_equation(r, emitter):
    disk = Strings(disc_tree(r), (1,))
    path = Strings(string_tree(r-1, [r]*3), (1, 1, 1))
    x, = map(v, disk.slots)
    c = coherence(disk.base, src(disk.base, x), tgt(disk.base, x))
    p = flat(disk.base, compare(disk.base, c, x))
    def change(shape, term):
        plus = shape.section([1]*len(shape.slots))
        return top_action(shape.base, shape.ctx, term, (shape.start, plus),
                          {i: row[0] for i, row in zip(shape.slots, shape.rows, strict=True)})
    def square(shape, edge, hu, hv):
        lo, hi = shape.start, shape.section([1]*len(shape.slots))
        return compare(shape.ctx, comp2(shape.ctx, r, subst_tm(edge, lo), hv),
                       comp2(shape.ctx, r, hu, subst_tm(edge, hi)))
    jc = square(disk, p, change(disk, c), change(disk, x))
    old, ctx = path.base, path.ctx
    a, b, d = map(v, path.slots)
    z = comp2(old, r-1, comp2(old, r-1, a, b), d)
    n = flat(old, z)
    assert z != n
    def specialize(w):
        tau = sub_from(disk.base, old, {x[1]: w})
        lifted = sub_from(disk.ctx, ctx, {disk.rows[0][0][1]: change(path, w)})
        return tau, subst_tm(p, tau), subst_tm(jc, lifted)
    lo, pz, jz = specialize(z)
    hi, pn, jn = specialize(n)
    l = flat(old, compare(old, z, n))
    dc = top_action(disk.base, old, c, (lo, hi), {x[1]: l})
    cz, cn = subst_tm(c, lo), subst_tm(c, hi)
    hz, hn, hcz, hcn = (change(path, w) for w in (z, n, cz, cn))
    left_square, right_square = square(path, l, hz, hn), square(path, dc, hcz, hcn)
    caps = (path.start, path.section((1, 1, 1)))
    def paste(f, g, jf, jg):
        fg = comp2(old, r, f, g)
        first = comp2(ctx, r, subst_tm(f, caps[0]), jg)
        second = comp2(ctx, r, jf, subst_tm(g, caps[1]))
        start = comp2(ctx, r, subst_tm(fg, caps[0]), hn)
        end = comp2(ctx, r, hcz, subst_tm(fg, caps[1]))
        moves = (compare(ctx, start, src(ctx, first)), first,
                 compare(ctx, tgt(ctx, first), src(ctx, second)), second, compare(ctx, tgt(ctx, second), end))
        return fg, composite(ctx, r+1, moves)
    upper, ju = paste(pz, l, jz, left_square)
    lower, jl = paste(dc, pn, right_square, jn)
    cross = compare(old, upper, lower)
    left = comp2(ctx, r+1, comp2(ctx, r, subst_tm(cross, caps[0]), hn), jl)
    right = comp2(ctx, r+1, ju, comp2(ctx, r, hcz, subst_tm(cross, caps[1])))
    assert left != right and infer(ctx, left) == infer(ctx, right)
    eq = compare(ctx, left, right)
    assert infer(ctx, eq) == arr(infer(ctx, left), left, right)
    if emitter:
        start = len(emitter.checks)
        certificate(emitter, ctx)('unary-temporal-associativity', eq, infer(ctx, eq))
        scope_checks(emitter, start, 'UnaryEquation')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    out = Emitter() if args.agda else None
    for r in (2, 3, 4):
        for reverse in (False, True):
            changed = example(r, reverse, out if r == 2 and not reverse else None)
            print(f'Rank {r}, event order {int(reverse)+1}: all lower labels literal, {changed} top rewritings.')
    for r in (1, 2, 3):
        unary_equation(r, out if r == 1 else None)
    print('Checked the temporal unary equation with all three top inputs moving in ranks 1 through 3.')
    if out:
        args.agda.write_text(out.module(args.agda.stem, 'Singleton and degeneracy factorizations.'))
