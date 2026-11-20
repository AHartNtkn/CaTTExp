"""Recover the simultaneous one-step template of a normalized globular substitution."""
from argparse import ArgumentParser
from pathlib import Path

from catt import (arr, comp2, infer, maximal_vars, src, sub_from, subst_tm, subst_ty, tdim,
                  tdim_tm, tgt, tree_ctx, tree_of, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_exterior_actions import certificate
from gray_normal_substitutions import blocks, compose, realize
from gray_partial_cylinder_sections import positions
from gray_spatial_units import compare, scope_checks
from gray_thin_substitution import flat
from gray_top_slot_promotion import expand, top_action
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import composite, string_tree


def truncate(tree, height):
    return tuple(truncate(child, height-1) for child in tree) if height else ()


class Rows:
    """String addresses, positions and projection onto the common truncation."""
    def __init__(self, ctx, s):
        self.ctx = ctx
        tree = tree_of(ctx)
        self.tree = truncate(tree, s)
        self.base = tree_ctx(self.tree)
        self.names = positions(tree)
        self.index = {key: i for i, key in enumerate(self.names)}
        self.base_index = {key: i for i, key in enumerate(positions(self.tree))}
        self.sites = [key[0] for key in self.base_index if len(key[0]) == s]
        self.poles = {a: [] for a in self.sites}
        collapse = []
        for i, (a, j) in enumerate(self.names):
            if len(a) == s+1:
                value = ident(self.base, v(self.base_index[a[:-1], 0]))
            elif len(a) == s:
                self.poles[a].append(i)
                value = v(self.base_index[a, 0])
            else:
                value = v(self.base_index[a, j])
            assert infer(self.base, value) == subst_ty(ctx[i], collapse)
            collapse.append(value)
        self.collapse = tuple(collapse)

    def section(self, offsets):
        return tuple(v(self.index[a, offsets.get(a, j)]) for a, j in self.base_index)


def template(qctx, pctx, sigma, r):
    s = r-1
    q, p = Rows(qctx, s), Rows(pctx, s)
    projected = tuple(subst_tm(z, p.collapse) for z in sigma)
    sizes, owned = {}, {}
    for a, row in q.poles.items():
        coordinates = [{p.names[i][0]: p.names[i][1] for i in top_counts(pctx, sigma[j])}
                       for j in row]
        owned[a] = set(coordinates[0])
        assert all(c.keys() == owned[a] for c in coordinates)
        for b in owned[a]:
            assert b not in sizes and coordinates[0][b] == 0
            assert coordinates[-1][b] == len(p.poles[b])-1
            sizes[b] = [right[b]-left[b] for left, right in zip(coordinates, coordinates[1:])]
            assert min(sizes[b], default=0) >= 0
    assert sizes.keys() == p.poles.keys()
    base_names = positions(p.tree)
    lengths = [sizes.get(base_names[i][0], []) for i in maximal_vars(p.base)]
    core, actual, subdivision = blocks(p.tree, lengths, r)
    assert actual.ctx == pctx
    full = Rows(core.ctx, s)
    alpha = []
    for i, (a, j) in enumerate(q.names):
        if len(a) < s:
            label = subst_tm(projected[i], full.section({}))
        elif len(a) == s:
            label = subst_tm(projected[i], full.section({b: j for b in owned[a]}))
        else:
            site, step = a[:-1], a[-1]
            before, after = [full.section({b: k for b in owned[site]}) for k in (step, step+1)]
            u, w = [projected[h] for h in q.poles[site][step:step+2]]
            moving = {p.base_index[b, 0]: v(full.index[b+(step,), 0]) for b in owned[site]}
            action = top_action(p.base, core.ctx, w, (before, after), moving)
            if action is None:
                action = ident(core.ctx, subst_tm(w, before))
            start = subst_tm(compare(p.base, u, w), before)
            label = flat(core.ctx, comp2(core.ctx, s, start, action))
        assert infer(core.ctx, label) == subst_ty(qctx[i], alpha)
        alpha.append(label)
    alpha = tuple(alpha)
    assert compose(qctx, pctx, alpha, subdivision, r) == sigma
    return core.ctx, alpha, subdivision


def example(r, reverse, emitter):
    s = r-1
    tree = string_tree(s-1, [s]*3)
    base = tree_ctx(tree)
    a, b, c = map(v, maximal_vars(base))
    first = (0, 0, 1) if not reverse else (1, 0, 0)
    groups = [[first, (), (1,)], [()], [(), (2,)]]
    words = [comp2(base, s-1, a, b), ident(base, tgt(base, b)), c]
    poles = []
    for word, group in zip(words, groups, strict=True):
        row = [word]
        for _ in group:
            row.append(comp2(base, s-1, ident(base, src(base, word)), row[-1]))
        poles.append(row)
    q, p, rho = realize(tree, s, groups, poles)
    core, alpha, f = template(q.ctx, p.ctx, rho, r)
    assert template(q.ctx, core, alpha, r) == (core, alpha, tuple(map(v, range(len(core)))))
    # Identical block sizes can carry different lower syntax at an interior position.
    variant = [row.copy() for row in poles]
    z = variant[0][1]
    variant[0][1] = comp2(base, s-1, z, ident(base, tgt(base, z)))
    _, _, alternate = realize(tree, s, groups, variant)
    other, beta, same_sizes = template(q.ctx, p.ctx, alternate, r)
    assert other == core and same_sizes == f
    position = tgt(q.ctx, q.rows[0][0])[1]
    assert alpha[position] != beta[position]
    for lengths in ([[2, 1], [0, 2], [0]], [[0, 0], [0, 0], [0]]):
        source, target, g = blocks(tree, lengths, r)
        assert source.ctx == p.ctx
        tau = compose(q.ctx, target.ctx, rho, g, r)
        core2, alpha2, h = template(q.ctx, target.ctx, tau, r)
        assert core2 == core and alpha2 == alpha and h == compose(core, target.ctx, f, g, r)
        if emitter and not any(map(sum, lengths)):
            start = len(emitter.checks)
            for name, domain, codomain, labels in (('template', q.ctx, core, alpha),
                                                    ('collapse', core, target.ctx, h)):
                arg, ret, sub = emitter.ctx(domain), emitter.ctx(codomain), emitter.sub(labels)
                emitter.checks.append(
                    f'{name} : {ret} ⊢sub {sub} ∶ {arg}\n'
                    f'{name} = from-just (checkSub {ret} (from-just (checkCtx {ret})) {sub} {arg})\n')
            scope_checks(emitter, start, 'Collapse')


def graft(ctx, r, active):
    tree = tree_of(ctx)
    addresses = positions(tree)
    wide, ends, edges = expand(tree, {addresses[i][0]: 1 for i in active})
    target = tree_ctx(wide)
    copies = tuple(tuple(map(v, end)) for end in ends)
    changes = {i: v(edge[0]) for i, edge in edges.items()}
    assert all(tdim_tm(ctx, v(i)) == r for i in changes)
    return target, copies, changes


def crossing(r, emitter):
    s = r-1
    tree = string_tree(s-1, [s]*2)
    base = tree_ctx(tree)
    a, b = map(v, maximal_vars(base))
    star = comp2(base, s-1, a, b)
    unit = ident(base, tgt(base, b))
    groups = [[(0, 0, 1)], [()]]
    poles = [[star, comp2(base, s-1, ident(base, src(base, star)), star)], [unit, unit]]
    q, p, rho = realize(tree, s, groups, poles)
    core, alpha, f = template(q.ctx, p.ctx, rho, r)
    _, target, g = blocks(tree, [[1, 2], [1]], r)
    end = target.ctx
    raw = tuple(subst_tm(z, g) for z in f)
    h = compose(core, end, f, g, r)
    assert raw != h
    head = ucomp(q.ctx)
    e = subst_tm(head, alpha)
    n = flat(core, e)
    assert e != n
    pure = compare(core, e, n)

    def temporal(ctx):
        return graft(ctx, r, [i for i, ty in enumerate(ctx) if tdim(ty)+1 == r])

    chart, parts, old_changes = temporal(core)
    final, caps, changes = temporal(end)
    def change(w):
        return top_action(end, final, w, caps, changes)
    def sides(ctx, path, copies, hu, hv):
        return (comp2(ctx, r, subst_tm(path, copies[0]), hv),
                comp2(ctx, r, hu, subst_tm(path, copies[1])))
    old_actions = [top_action(core, chart, z, parts, old_changes) for z in (e, n)]
    jc = compare(chart, *sides(chart, pure, parts, *old_actions))
    def specialize(sub):
        lab = {}
        for i, z in enumerate(sub):
            for sign in (0, 1):
                lab[parts[sign][i][1]] = subst_tm(z, caps[sign])
            if i in old_changes:
                lab[old_changes[i][1]] = change(z)
        labels = tuple(lab[i] for i in range(len(chart)))
        for i, z in enumerate(labels):
            assert infer(final, z) == subst_ty(chart[i], labels[:i])
        edge = subst_tm(pure, sub)
        u, w = (subst_tm(z, sub) for z in (e, n))
        square = subst_tm(jc, labels)
        assert (src(final, square), tgt(final, square)) == sides(final, edge, caps, change(u), change(w))
        return edge, square
    pg, jg = specialize(raw)
    ph, jh = specialize(h)
    deltas = {i: compare(end, raw[i], h[i]) for i in old_changes}
    def promote(z):
        return top_action(core, end, z, (raw, h), deltas)
    de, dn = promote(e), promote(n)
    local = {i: promote(z) for i, z in enumerate(alpha) if tdim_tm(q.ctx, v(i)) == r}
    a0, a1 = (tuple(subst_tm(z, sub) for z in alpha) for sub in (raw, h))
    assert top_action(q.ctx, end, head, (a0, a1), {i: t for i, t in local.items() if t}) == de

    def square(edge):
        return compare(final, *sides(final, edge, caps, change(src(end, edge)), change(tgt(end, edge))))
    def paste(x, y, jx, jy):
        xy = comp2(end, r, x, y)
        start, finish = sides(final, xy, caps, change(src(end, x)), change(tgt(end, y)))
        first = comp2(final, r, subst_tm(x, caps[0]), jy)
        last = comp2(final, r, jx, subst_tm(y, caps[1]))
        terms = (compare(final, start, src(final, first)), first,
                 compare(final, tgt(final, first), src(final, last)), last,
                 compare(final, tgt(final, last), finish))
        return xy, composite(final, r+1, terms)
    left, jl = paste(pg, dn, jg, square(dn))
    right, jr = paste(de, ph, square(de), jh)
    eta = compare(end, left, right)
    initial, terminal = change(src(end, left)), change(tgt(end, left))
    one = comp2(final, r+1, comp2(final, r, subst_tm(eta, caps[0]), terminal), jr)
    two = comp2(final, r+1, jl, comp2(final, r, initial, subst_tm(eta, caps[1])))
    assert one != two and infer(final, one) == infer(final, two)
    filling = compare(final, one, two)
    expected = arr(infer(final, one), one, two)
    assert infer(final, filling) == expected and not top_counts(final, filling)
    if emitter:
        start = len(emitter.checks)
        certificate(emitter, final)('subdivision-crossing', filling, expected)
        scope_checks(emitter, start, 'Crossing')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    out = Emitter() if args.agda else None
    for r in (2, 3, 4):
        for reverse in (False, True):
            example(r, reverse, out if r == 2 and not reverse else None)
        print(f'Rank {r}: recovered the same template after mixed and total collapse.', flush=True)
    for r in (2, 3):
        crossing(r, out if r == 2 else None)
        print(f'Rank {r}: checked the specialized mixed crossing on the branching template.', flush=True)
    if out:
        args.agda.write_text(out.module(args.agda.stem, 'Simultaneous subdivision templates.'))
