"""Check the stacked spatial compositor and the crossing of a thin bridge."""
from argparse import ArgumentParser
from collections import defaultdict
from functools import cache
from itertools import product
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, glue_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, subst_ty, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_exterior_actions import certificate, coherence
from gray_partial_cylinder_sections import positions
from gray_penultimate_partial_actions import rebracket
from gray_top_slot_promotion import expand, top_action
from rc2 import kappa, rc2_full
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import composite, string_tree


def strip(width, stages, vertices, columns):
    """The ordinary edge graph and the directed face rules of the opposed strip."""
    def point(i, t):
        return (i, t if i in vertices else 0)
    def edge(i, t):
        return ('h', i, t if i in columns else 0)
    def vertical(i, t):
        return (('v', i, t),) if i in vertices else ()
    edges, rules = {}, {}
    for i in range(width+1):
        for t in range(stages+1):
            if i < width:
                edges[edge(i, t)] = (point(i, t), point(i+1, t))
            if t < stages and i in vertices:
                edges[vertical(i, t)[0]] = (point(i, t), point(i, t+1))
            if t < stages and i in columns:
                rules[i, t] = (vertical(i, t)+(edge(i, t+1),), (edge(i, t),)+vertical(i+1, t))
    return edges, rules


def check_schedules(width, stages):
    masks = paths = multiple = 0
    for bits in product((False, True), repeat=2*width+1):
        vertices = {i for i in range(width+1) if bits[i]}
        columns = {i for i in range(width) if bits[width+1+i]}
        if any(i not in columns and vertices & {i, i+1} for i in range(width)):
            continue
        masks += 1
        edges, rules = strip(width, stages, vertices, columns)
        outgoing = defaultdict(list)
        for e, (a, b) in edges.items():
            outgoing[a].append((e, b))

        @cache
        def walks(a):
            return [()] + [(e, *p) for e, b in outgoing[a] for p in walks(b)]

        @cache
        def schedules(p):
            by_target = defaultdict(set)
            by_target[p].add(())
            for move, (old, new) in rules.items():
                for i in range(len(p)-len(old)+1):
                    if p[i:i+len(old)] != old:
                        continue
                    q = p[:i]+new+p[i+len(old):]
                    for target, tails in schedules(q).items():
                        by_target[target].update((move, *tail) for tail in tails)
            return by_target

        for a in {u for pair in edges.values() for u in pair}:
            for p in walks(a):
                paths += 1
                for orders in schedules(p).values():
                    if len(orders) == 1:
                        continue
                    multiple += 1
                    root = next(iter(orders))
                    seen, todo = {root}, [root]
                    while todo:
                        word = todo.pop()
                        for j in range(len(word)-1):
                            other = word[:j]+(word[j+1], word[j])+word[j+2:]
                            if other in orders and other not in seen:
                                assert word[j][0] != word[j+1][0]
                                seen.add(other)
                                todo.append(other)
                    assert seen == orders
    print(f'{masks} masks, {paths} paths, {multiple} pairs with multiple schedules.', flush=True)


class Chart:
    def __init__(self):
        self.ctx = ()

    def cell(self, a=None, b=None):
        ty = STAR if a is None else arr(infer(self.ctx, a), a, b)
        if a is not None:
            assert infer(self.ctx, a) == infer(self.ctx, b)
        x = v(len(self.ctx))
        self.ctx += (ty,)
        return x

    def h(self, a, b):
        return comp2(self.ctx, 0, a, b)

    def chain(self, *terms):
        return composite(self.ctx, 1, terms)

    def route(self, start, steps, end):
        path, here = [], start
        for cell in steps:
            if here != src(self.ctx, cell):
                path.append(kappa(self.ctx, here, src(self.ctx, cell)))
            path.append(cell)
            here = tgt(self.ctx, cell)
        if here != end:
            path.append(kappa(self.ctx, here, end))
        return self.chain(*path)

    def along_path(self, f0, g0, f1, g1, start, end, left, right):
        return self.route(self.h(start, self.h(f1, g1)),
                          [self.h(left, g1), self.h(f0, right)], self.h(self.h(f0, g0), end))

    def along_stages(self, lo, hi, a, b, c, d, before, after):
        return self.route(self.h(self.h(a, b), hi),
                          [self.h(a, after), self.h(before, d)], self.h(lo, self.h(c, d)))


def rectangle():
    ch = Chart()
    points = [[ch.cell() for _ in range(3)] for _ in range(3)]
    x = [[ch.cell(row[i], row[i+1]) for i in range(2)] for row in points]
    y = [[ch.cell(points[t][i], points[t+1][i]) for i in range(3)] for t in range(2)]
    faces = [[ch.cell(ch.h(y[t][i], x[t+1][i]), ch.h(x[t][i], y[t][i+1]))
              for i in range(2)] for t in range(2)]
    cols = [ch.along_stages(x[0][i], x[2][i], y[0][i], y[1][i], y[0][i+1], y[1][i+1],
                            faces[0][i], faces[1][i]) for i in range(2)]
    one = ch.along_path(*x[0], *x[2], ch.h(y[0][0], y[1][0]), ch.h(y[0][2], y[1][2]), *cols)
    rows = [ch.along_path(*x[t], *x[t+1], y[t][0], y[t][2], *faces[t]) for t in range(2)]
    two = ch.along_stages(ch.h(*x[0]), ch.h(*x[2]), y[0][0], y[1][0], y[0][2], y[1][2], *rows)
    assert infer(ch.ctx, one) == infer(ch.ctx, two) and one != two
    assert top_counts(ch.ctx, one) == top_counts(ch.ctx, two) == {z[1]: 1 for row in faces for z in row}
    w = rc2_full(ch.ctx, one, two)
    assert infer(ch.ctx, w) == arr(infer(ch.ctx, one), one, two)
    print('Checked both orders of pasting four positive spatial squares.', flush=True)


def bridge():
    ch = Chart()
    points = [[ch.cell() for _ in range(4)] for _ in range(2)]
    edges = []
    for a, b, c, d in points:
        edges.append((ch.cell(a, b), ch.cell(c, d), ch.cell(a, c), ch.cell(b, d)))
    (p0, q0, u0, v0), (p1, q1, u1, v1) = edges
    e, f, ee, ff = [ch.cell(a, b) for a, b in zip(*points)]
    P = ch.cell(ch.h(e, p1), ch.h(p0, f))
    Q = ch.cell(ch.h(ee, q1), ch.h(q0, ff))
    U = ch.cell(ch.h(e, u1), ch.h(u0, ee))
    V = ch.cell(ch.h(f, v1), ch.h(v0, ff))
    k0, k1 = [ch.cell(ch.h(p, v_), ch.h(u, q)) for p, q, u, v_ in edges]
    # Boundary obtained by opposing the middle degree of the depth-two action.
    ja = ch.along_path(p0, v0, p1, v1, e, ff, P, V)
    jb = ch.along_path(u0, q0, u1, q1, e, ff, U, Q)
    shell_a = ch.chain(ja, ch.h(k0, ff))
    shell_b = ch.chain(ch.h(e, k1), jb)
    # Independently paste the two temporal actions on the pure crossing's poles.
    first = ch.along_stages(u0, v1, p0, f, q0, ff, k0, V)
    last = ch.along_stages(u0, v1, e, p1, ee, q1, U, k1)
    want_a = ch.chain(ch.h(P, v1), first)
    want_b = ch.chain(last, ch.h(u0, Q))
    prefix = kappa(ch.ctx, src(ch.ctx, want_a), src(ch.ctx, shell_a))
    suffix = kappa(ch.ctx, tgt(ch.ctx, shell_a), tgt(ch.ctx, want_a))
    left = rc2_full(ch.ctx, want_a, ch.chain(prefix, shell_a, suffix))
    right = rc2_full(ch.ctx, ch.chain(prefix, shell_b, suffix), want_b)
    cube = ch.cell(shell_a, shell_b)
    check_ctx(ch.ctx)
    framed = ch.chain(prefix, cube, suffix)
    result = composite(ch.ctx, 2, (left, framed, right))
    ty = arr(infer(ch.ctx, want_a), want_a, want_b)
    assert infer(ch.ctx, result) == ty and top_counts(ch.ctx, result) == {cube[1]: 1}
    print('Turned the opposed depth-two face into the temporal crossing with its prescribed two poles.', flush=True)
    return ch.ctx, result, ty


def sliced(r, sizes):
    """Realize the binary reduction on two slots with three distinct collapsed pole writings."""
    base = glue_tree(r, r-1, r)
    old = tree_ctx(base)
    slots = maximal_vars(old)
    names = positions(base)

    def build(lengths):
        return expand(base, {names[i][0]: n for i, n in zip(slots, lengths) if n})
    first, second = sizes
    full_tree, (start, _), edges = build([a+b for a, b in zip(first, second)])
    full = tree_ctx(full_tree)

    def slab(lengths, offsets):
        tree, (lo, hi), local_edges = build(lengths)
        ctx = tree_ctx(tree)
        lab = [None]*len(ctx)
        for i, j in enumerate(lo):
            lab[j] = v(start[i])
        values = {}
        for i, n, offset in zip(slots, lengths, offsets):
            all_edges = edges.get(i, [])
            selected = all_edges[offset:offset+n]
            corner = tgt(full, v(all_edges[offset-1])) if offset else v(start[i])
            lab[lo[i]] = corner
            for j, z in zip(local_edges.get(i, []), selected, strict=True):
                lab[j] = v(z)
                lab[tgt(ctx, v(j))[1]] = tgt(full, v(z))
            if n:
                shape = tree_ctx(string_tree(r, [r+1]*n))
                sigma = sub_from(shape, ctx, dict(zip(maximal_vars(shape), map(v, local_edges[i]), strict=True)))
                values[i] = subst_tm(ucomp(shape), sigma)
            else:
                values[i] = ident(ctx, v(lo[i]))
        for j, arg in enumerate(lab):
            assert infer(full, arg) == subst_ty(ctx[j], lab[:j])
        ends = (tuple(map(v, lo)), tuple(map(v, hi)))
        def apply(term):
            return subst_tm(term, lab)
        def raised(term):
            return top_action(old, ctx, term, ends, values)
        return ctx, ends, apply, raised

    zero = (0,)*len(slots)
    a, ae, ai, da = slab(first, zero)
    b, be, bi, db = slab(second, first)
    c, ce, ci, dc = slab([x+y for x, y in zip(first, second)], zero)
    assert c == full
    w = ucomp(old)
    x = comp2(old, r-1, ident(old, src(old, w)), w)
    y = comp2(old, r-1, w, ident(old, tgt(old, w)))
    assert len({x, y, w}) == 3 and infer(old, x) == infer(old, y) == infer(old, w)
    ab, bc, ac = (coherence(old, s, t) for s, t in ((x, w), (w, y), (x, y)))
    f = coherence(a, subst_tm(x, ae[0]), subst_tm(w, ae[1]))
    g = coherence(b, subst_tm(w, be[0]), subst_tm(y, be[1]))
    normal = coherence(c, subst_tm(x, ce[0]), subst_tm(y, ce[1]))
    fa, ga = comp2(a, r, subst_tm(ab, ae[0]), da(w)), comp2(b, r, subst_tm(bc, be[0]), db(y))
    ca = comp2(c, r, subst_tm(ac, ce[0]), dc(y))
    assert ai(tgt(a, f)) == bi(src(b, g))
    left, right = ai(f), bi(g)
    actual = comp2(full, r, left, right)
    assert infer(full, actual) == infer(full, normal)
    steps = []
    current = actual

    def advance(step, letters):
        nonlocal current
        change = rebracket(full, r, letters, current, src(full, step))
        if change is not None:
            steps.append(change)
        steps.append(step)
        current = tgt(full, step)

    h = lambda s, t: comp2(full, r, s, t)
    ba, du, mid, dv = ai(subst_tm(ab, ae[0])), ai(da(w)), bi(subst_tm(bc, be[0])), bi(db(y))
    early, split = ai(subst_tm(bc, ae[0])), ai(da(y))
    assert mid == ai(subst_tm(bc, ae[1]))
    advance(h(ai(coherence(a, f, fa)), right), [left, right])
    advance(h(ai(fa), bi(coherence(b, g, ga))), [ai(fa), right])
    square = ai(coherence(a, comp2(a, r, da(w), subst_tm(bc, ae[1])),
                          comp2(a, r, subst_tm(bc, ae[0]), da(y))))
    advance(h(h(ba, square), dv), [ba, du, mid, dv])
    bridge_product = subst_tm(coherence(old, comp2(old, r, ab, bc), ac), ce[0])
    advance(h(bridge_product, h(split, dv)), [ba, early, split, dv])
    join = coherence(full, h(split, dv), dc(y))
    lower = subst_tm(ac, ce[0])
    advance(h(lower, join), [lower, split, dv])
    advance(coherence(full, ca, normal), [ca])
    witness = composite(full, r+1, steps)
    assert infer(full, witness) == arr(infer(full, actual), actual, normal)
    assert not top_counts(full, witness) and top_counts(full, actual) == top_counts(full, normal)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--width', type=int, default=3)
    parser.add_argument('--stages', type=int, default=2)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if min(args.width, args.stages) < 1:
        parser.error('use positive strip sizes')
    check_schedules(args.width, args.stages)
    for r in (1, 2, 3):
        for sizes in (((1, 1), (1, 2)), ((2, 0), (0, 1)), ((0, 0), (2, 1)), ((0, 0), (0, 0))):
            sliced(r, sizes)
    print('Checked twelve binary folds at three distinct lower writings, including empty portions.', flush=True)
    rectangle()
    ctx, w, ty = bridge()
    if args.agda:
        out = Emitter()
        certificate(out, ctx)('temporal-crossing', w, ty)
        args.agda.write_text(out.module(args.agda.stem, 'Transport of the depth-two cube boundary.'))
