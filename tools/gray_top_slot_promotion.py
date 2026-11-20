"""Check top-slot promotion in a partially marked pasting arity, including spatial stacks."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from pathlib import Path

from catt import (STAR, arr, chain_tree, check_ctx, comp2, disc_tree, fv_tm, fv_ty, glue_tree,
                  infer, maximal_vars, ps_dim, src, sub_from, subst_tm, subst_ty, tdim_tm,
                  tgt, tree_ctx, tree_of, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_exterior_actions import certificate, coherence
from gray_leaf_naturality import marked_leaves
from gray_partial_cylinder_sections import positions
from gray_penultimate_partial_actions import data
from gray_temporal_partial_actions import action
from rc2 import functor
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import string_tree


def support(ctx, t):
    return fv_tm(t) | fv_ty(infer(ctx, t))


def top_action(source, target, t, copies, changes):
    """Depth zero, by grafting the marked top leaves of each actual head."""
    @cache
    def go(w):
        if not (support(source, w) & changes.keys()):
            return None
        if w[0] == 'v':
            return changes[w[1]]
        _, arity, ty, args = w
        slots = maximal_vars(arity)
        active = {i: h for i in slots if (h := go(args[i])) is not None}
        assert active and all(tdim_tm(source, args[i]) == tdim_tm(source, w) for i in active)
        head = ('coh', arity, ty, tuple(map(v, range(len(arity)))))
        base = {i: subst_tm(args[i], copies[0]) for i in slots}
        out = functor(target, None, arity, tree_of(arity), head, base, active)
        assert (src(target, out), tgt(target, out)) == tuple(subst_tm(w, cp) for cp in copies)
        return out
    return go(t)


def expand(tree, lengths):
    names = positions(tree)
    def visit(children, addr):
        if addr in lengths:
            assert not children
            return chain_tree(lengths[addr])
        return tuple(visit(child, addr+(i,)) for i, child in enumerate(children))
    wide = visit(tree, ())
    wide_names = {p: i for i, p in enumerate(positions(wide))}
    start = [wide_names[p] for p in names]
    end = [wide_names[addr, lengths[addr]] if addr in lengths else i for i, (addr, _) in zip(start, names)]
    stacks = {i: [wide_names[addr+(j,), 0] for j in range(lengths[addr])]
              for i, (addr, _) in enumerate(names) if addr in lengths}
    return wide, (start, end), stacks


def time_inclusion(from_ctx, from_copies, from_changes, to_copies, to_changes, old_map):
    inclusion = [None]*len(from_ctx)
    for i, j in enumerate(old_map):
        for e in (0, 1):
            inclusion[from_copies[e][i][1]] = to_copies[e][j]
        if i in from_changes:
            inclusion[from_changes[i][1]] = to_changes[j]
    assert None not in inclusion
    return tuple(inclusion)


def opposed_spatial_context(time, moving, r):
    """Reverse degree r+2 in the ordinary depth-one spatial cylinder."""
    dom = ()
    ends = [[], []]
    shifts = {}
    for i, ty in enumerate(time):
        for e in (0, 1):
            if not e or i in moving:
                arg = v(len(dom))
                dom += (subst_ty(ty, ends[e]),)
            ends[e].append(arg)
        if i not in moving:
            assert subst_ty(ty, ends[0]) == subst_ty(ty, ends[1])
            continue
        a, b = ends[0][i], ends[1][i]
        if tdim_tm(time, v(i)) == r+1:
            hs = top_action(time, dom, ty[2], ends, shifts)
            ht = top_action(time, dom, ty[3], ends, shifts)
            # Opposing the top changes reverses the time-then-space orientation.
            a, b = comp2(dom, r, hs, b), comp2(dom, r, a, ht)
        assert infer(dom, a) == infer(dom, b)
        shifts[i] = v(len(dom))
        dom += (arr(infer(dom, a), a, b),)
    check_ctx(dom)
    return dom, ends, shifts


def ordinary_faces(ctx, old, t, copies, time_action):
    poles = [[], []]
    a = b = t
    while infer(old, a) != STAR:
        a, b = src(old, a), tgt(old, b)
        poles[0].append(b)
        poles[1].append(a)
    out = []
    for e, cp in enumerate(copies):
        cap = subst_tm(t, cp)
        for k, x in enumerate(reversed(poles[e])):
            h = time_action(x)
            if h is not None:
                cap = comp2(ctx, k, h, cap) if e else comp2(ctx, k, cap, h)
        out.append(cap)
    return out


def bridge_composite(old, wide, target, wc, wide_marks, r, sp, inclusions,
                     raw, raised, result, old_action, lifted):
    """Assemble a composition head with independently written signed boundaries."""
    other = comp2(old, r-1, ident(old, src(old, raw)), raw)
    bridge = coherence(old, other, raw)
    lower = subst_tm(bridge, sp[0])
    m = r+1
    candidate = comp2(wide, r, lower, raised)
    source, final = src(wide, candidate), tgt(wide, candidate)
    generic = coherence(wide, source, final)
    # The temporal action on the two factors uses their actual common side.
    shape = glue_tree(m, r, m)
    arity = tree_ctx(shape)
    lab = sub_from(arity, wide, dict(zip(maximal_vars(arity), (lower, raised), strict=True)))
    selected = frozenset(i for i, arg in enumerate(lab) if support(wide, arg) & wide_marks)
    binary, chart, _ = action(shape, selected)
    _, cc, ch = data(arity, selected)
    labels = dict(lifted)
    labels[source] = subst_tm(old_action(other), inclusions[0])
    labels[lower] = subst_tm(old_action(bridge), inclusions[0])
    labels[raised] = result
    sigma = [None]*len(chart)
    for i, arg in enumerate(lab):
        for e in (0, 1):
            sigma[cc[e][i][1]] = subst_tm(arg, wc[e])
        if i in ch:
            sigma[ch[i][1]] = labels[arg]
    h = subst_tm(binary, sigma)
    nominal = ordinary_faces(target, wide, candidate, wc, labels.__getitem__)
    assert (src(target, h), tgt(target, h)) == tuple(nominal)
    # Change the full-support cap writing on both pure copies.
    for e in (0, 1):
        a, b = (candidate, generic) if e else (generic, candidate)
        adjust = subst_tm(coherence(wide, a, b), wc[e])
        pole = generic
        rails = []
        for _ in range(m):
            pole = (src if e else tgt)(wide, pole)
            rails.append(labels[pole])
        for k, rail in enumerate(reversed(rails)):
            if rail is not None:
                adjust = comp2(target, k, rail, adjust) if e else comp2(target, k, adjust, rail)
        h = comp2(target, m, h, adjust) if e else comp2(target, m, adjust, h)
    wanted = ordinary_faces(target, wide, generic, wc, labels.__getitem__)
    assert (src(target, h), tgt(target, h)) == tuple(wanted)
    assert top_counts(target, h) == top_counts(target, result)
    return h, arr(infer(target, wanted[0]), *wanted)


def check(tree, marks, lengths, old_action, label, emitter=None, actual=None, alternative=False):
    old = tree_ctx(tree)
    r = ps_dim(old)
    wide_tree, (start, end), stacks = expand(tree, lengths)
    wide = tree_ctx(wide_tree)
    time, copies, change = data(old, marks)
    wide_marks = {start[i] for i in marks}
    for i, edges in stacks.items():
        if i in marks:
            wide_marks.update(edges)
            wide_marks.update(tgt(wide, v(g))[1] for g in edges)
    target, wc, wh = data(wide, wide_marks)
    moving = {c[i][1] for i in stacks for c in copies}
    moving.update(change[i][1] for i in stacks if i in marks)
    dom, space_ends, space_h = opposed_spatial_context(time, moving, r)
    values = [None]*len(dom)
    inclusions = [time_inclusion(time, copies, change, wc, wh, endpoint) for endpoint in (start, end)]
    for i in range(len(time)):
        for p in (0, 1):
            values[space_ends[p][i][1]] = inclusions[p][i]

    stack_terms = {}
    for i, edges in stacks.items():
        shape = string_tree(r, [r+1]*len(edges))
        ar = tree_ctx(shape)
        inc = sub_from(ar, wide, dict(zip(maximal_vars(ar), map(v, edges), strict=True)))
        stack_terms[i] = subst_tm(ucomp(ar), inc)
        for e in (0, 1):
            j = space_h[copies[e][i][1]][1]
            values[j] = subst_tm(stack_terms[i], wc[e])
        if i in marks:
            selected = frozenset(j for j, x in enumerate(inc) if x[1] in wide_marks)
            h, chart, _ = action(shape, selected)
            _, cc, ch = data(ar, selected)
            sigma = time_inclusion(chart, cc, ch, wc, wh, [x[1] for x in inc])
            values[space_h[change[i][1]][1]] = subst_tm(h, sigma)

    values = tuple(values)
    assert None not in values
    for j, arg in enumerate(values):
        assert infer(target, arg) == subst_ty(dom[j], values[:j])
    raw = ucomp(old)
    if alternative:
        raw = comp2(old, r-1, raw, ident(old, tgt(old, raw)))
    h = old_action(raw)
    assert h is not None
    base = ordinary_faces(time, old, raw, copies, old_action)
    assert (src(time, h), tgt(time, h)) == tuple(base)
    # The two computations below use distinct contexts and substitutions.
    hs, ht = [top_action(time, dom, boundary, space_ends, space_h) for boundary in base]
    h0, h1 = [subst_tm(h, cp) for cp in space_ends]
    a, b = comp2(dom, r, hs, h1), comp2(dom, r, h0, ht)
    given = arr(infer(dom, a), a, b)
    sp = (tuple(map(v, start)), tuple(map(v, end)))
    raised = top_action(old, wide, raw, sp, stack_terms)
    faces = [subst_tm(raw, cp) for cp in sp]
    assert (src(wide, raised), tgt(wide, raised)) == tuple(faces)
    lifted = {f: subst_tm(h, inc) for f, inc in zip(faces, inclusions)}
    x, y = raw, raw
    for _ in range(r):
        x, y = src(old, x), tgt(old, y)
        for z in (x, y):
            hz = old_action(z)
            lifted[subst_tm(z, sp[0])] = subst_tm(hz, inclusions[0]) if hz is not None else None
    desired = ordinary_faces(target, wide, raised, wc, lifted.__getitem__)
    wanted = arr(infer(target, desired[0]), *desired)
    assert subst_ty(given, values) == wanted

    if actual == 'variable':
        assert h[0] == 'v'
        witness = space_h[h[1]]
    elif actual == 'disjoint':
        assert not (marks & stacks.keys()) and moving <= set(maximal_vars(time))
        ar, _ = marked_leaves(time, frozenset(moving))
        assert ar == dom
        # Both ends already inhabit the same promoted globular pasting arity.
        witness = coherence(dom, a, b)
    else:
        witness = None

    if witness is not None:
        assert infer(dom, witness) == given
        result = subst_tm(witness, values)
        assert infer(target, result) == wanted
        top = Counter(wh[j][1] for i in marks & stacks.keys() for j in stacks[i])
        assert top_counts(target, result) == top
        if actual == 'disjoint':
            bridge_h, bridge_ty = bridge_composite(old, wide, target, wc, wide_marks, r, sp,
                                                   inclusions, raw, raised, result, old_action, lifted)
            if emitter:
                certificate(emitter, target)(label+'-bridge', bridge_h, bridge_ty)
    if emitter:
        g, p, sig = emitter.ctx(target), emitter.ctx(dom), emitter.sub(values)
        given_ty, wanted_ty = emitter.ty(given), emitter.ty(wanted)
        emitter.checks.append(
            f'{label}-sub : {g} ⊢sub {sig} ∶ {p}\n'
            f'{label}-sub = from-just (checkSub {g} (from-just (checkCtx {g})) {sig} {p})\n'
            f'{label} : ∀ {{j}} → {p} ⊢tm j ∶ {given_ty} → {g} ⊢tm j [ {sig} ]tm ∶ {wanted_ty}\n'
            f'{label} j = S.tm[] (λ ()) j {label}-sub\n')
        if witness is not None:
            emitter.check_type(label+'-witness', target, result, wanted)


def run(r, emitter):
    disc = disc_tree(r)
    disc_ctx = tree_ctx(disc)
    marks = frozenset({1, *range(2, len(disc_ctx))})
    _, _, ch = data(disc_ctx, marks)
    check(disc, marks, {(0,)*r: 3}, lambda x: ch.get(x[1]), 'one-ended-stack', emitter, 'variable')

    # Low branching, a moving one-edge leaf and unequal transverse stacks.
    tree = ((), disc_tree(r-1), disc_tree(r-1))
    ar = tree_ctx(tree)
    small, a, b = maximal_vars(ar)
    names = positions(tree)
    for active, stacks, tag, concrete in [
        ({small, a}, {a: 2, b: 3}, 'mixed-stacks', None),
        ({small, b}, {a: 2}, 'disjoint', 'disjoint')]:
        selected = frozenset(active)
        _, lift = marked_leaves(ar, selected)
        check(tree, selected, {names[i][0]: size for i, size in stacks.items()}, lift, tag,
              emitter, concrete, alternative=True)
    # A genuinely deep single-rank selection incident to both top slots.
    tree = glue_tree(r, r-1, r)
    ar = tree_ctx(tree)
    selected = frozenset({0, *range(2, len(ar))}) if r > 1 else frozenset(range(len(ar)))
    _, _, ch = data(ar, selected)
    term, _, _ = action(tree, selected)
    w = ucomp(ar)
    names = positions(tree)
    check(tree, selected, {names[i][0]: 2+j for j, i in enumerate(maximal_vars(ar))},
          lambda z: term if z == w else ch.get(z[1]), 'deep-incident', emitter)
    print(f'Rank {r}: four transposed substitutions, two concrete fillers and two unequal stacks.', flush=True)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('rank', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.rank < 2:
        parser.error('use a base rank of at least two')
    emitter = Emitter() if args.agda else None
    if emitter:
        emitter.checks.append('import CaTTExp.Subst ∅ cattSide as S')
    for r in range(2, args.rank+1):
        run(r, emitter if r == args.rank else None)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Opposed spatial promotion in a partial cylinder.'))
