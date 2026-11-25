"""Check the mixed rank-four generator boundaries and positional loop erasure."""
from argparse import ArgumentParser
from itertools import permutations, product
from pathlib import Path

from catt import (arr, chain_tree, comp2, disc_tree, glue_tree, infer, maximal_vars, src,
                  sub_from, subst_tm, subst_ty, tdim, tgt, tree_ctx, ucomp, v)
from catt_unit_ordered_exchange import temporal_words
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from rc_oracle import strict_image
from relative_coherence_exchange_faces import head, reassociate
from relative_coherence_hidden_seam import identity
from relative_coherence_interval_generator import trees
from semistrict_surface_exact_boundary import check_retraction
from steiner import Complex, image_to_cell, raise_to, support


def check_prism(left_moves, emitter):
    shape = (3, 2) if left_moves else (2, 3)
    ctx = tree_ctx(glue_tree(shape[0], 0, shape[1]))
    x, y = map(v, maximal_vars(ctx))
    change = x if left_moves else y
    first, last = src(ctx, change), tgt(ctx, change)
    bare = tree_ctx(glue_tree(2, 0, 2))
    a, b = maximal_vars(bare)
    early, late = temporal_words(bare, v(a), v(b), 0, 1)
    crossing = head(bare, late, early)

    def square_at(event):
        pair = (event, y) if left_moves else (x, event)
        return subst_tm(crossing, sub_from(bare, ctx, dict(zip((a, b), pair, strict=True))))

    def beside(u, w):
        return comp2(ctx, 0, u, w)

    if left_moves:
        early_change = comp2(ctx, 1, beside(change, src(ctx, y)), beside(tgt(ctx, first), y))
        late_change = comp2(ctx, 1, beside(src(ctx, first), y), beside(change, tgt(ctx, y)))
    else:
        early_change = comp2(ctx, 1, beside(x, src(ctx, first)), beside(tgt(ctx, x), change))
        late_change = comp2(ctx, 1, beside(src(ctx, x), change), beside(x, tgt(ctx, first)))
    cross_first = comp2(ctx, 2, square_at(first), early_change)
    update_first = comp2(ctx, 2, late_change, square_at(last))
    start, end = (cross_first, update_first) if left_moves else (update_first, cross_first)
    ty = infer(ctx, start)
    assert ty == infer(ctx, end)
    name = 'left' if left_moves else 'right'
    prism = head(ctx, start, end)
    emitter.check_type(name + 'Prism', ctx, prism, arr(ty, start, end))
    emitter.checks.append(f'{name}Reverse : graySide {emitter.ctx(ctx)} {emitter.ty(ty)} '
                          f'{emitter.tm(end)} {emitter.tm(start)} ≡ false\n{name}Reverse = refl\n')
    return ctx, prism


def check_missing_join(emitter, left_prism, right_prism):
    ctx = tree_ctx(glue_tree(3, 0, 3))
    a, b = map(v, maximal_vars(ctx))
    bare = tree_ctx(glue_tree(2, 0, 2))
    i, j = maximal_vars(bare)
    early, late = temporal_words(bare, v(i), v(j), 0, 1)
    cross = head(bare, late, early)
    schedules, steps_by_word, edges = {}, {}, set()
    for perm in permutations('ABC'):
        word = ''.join(perm)
        x, y = src(ctx, a), src(ctx, b)
        steps = []
        for pos, event in enumerate(word):
            if event == 'C':
                steps.append(subst_tm(cross, sub_from(bare, ctx, {i: x, j: y})))
                continue
            left, right = (a, y) if event == 'A' else (x, b)
            # Vary one argument of the relevant chronological 2-layer.
            if 'C' in word[:pos]:
                l = comp2(ctx, 0, left, src(ctx, y))
                r = comp2(ctx, 0, tgt(ctx, x), right)
            else:
                l = comp2(ctx, 0, src(ctx, x), right)
                r = comp2(ctx, 0, left, tgt(ctx, y))
            steps.append(comp2(ctx, 1, l, r))
            if event == 'A':
                x = tgt(ctx, a)
            else:
                y = tgt(ctx, b)
        steps_by_word[word] = steps
        schedules[word] = comp2(ctx, 2, comp2(ctx, 2, steps[0], steps[1]), steps[2])
        for pos in range(2):
            pair = word[pos:pos + 2]
            # Left and right prisms. The inner square reads right interval first.
            inner = 'BA' if 'C' in word[:pos] else 'AB'
            if pair in ('CA', 'BC', inner):
                edges.add((word, word[:pos] + pair[::-1] + word[pos + 2:]))
    assert len(set(infer(ctx, t) for t in schedules.values())) == 1
    reached = {'BCA'}
    pending = list(reached)
    while pending:
        current = pending.pop()
        for source, target in edges:
            if source == current and target not in reached:
                reached.add(target)
                pending.append(target)
    assert len(edges) == 6 and reached == set(schedules) - {'ABC'}
    for word, term in schedules.items():
        emitter.check_typed('schedule' + word, ctx, term)
    s, t = schedules['BCA'], schedules['ABC']
    emitter.checks.append(f'joinHead : graySide {emitter.ctx(ctx)} {emitter.ty(infer(ctx, s))} '
                          f'{emitter.tm(s)} {emitter.tm(t)} ≡ false\njoinHead = refl\n')
    prism_ctx, prism = left_prism
    prism_slots = dict(zip(maximal_vars(prism_ctx), (a, tgt(ctx, b)), strict=True))
    placed = subst_tm(prism, sub_from(prism_ctx, ctx, prism_slots))
    step = comp2(ctx, 2, steps_by_word['BCA'][0], placed)
    start = reassociate(ctx, steps_by_word['BCA'], False)
    end = reassociate(ctx, steps_by_word['BAC'], True)
    fitted = comp2(ctx, 3, comp2(ctx, 3, start, step), end)
    emitter.check_type('rawToBAC', ctx, fitted, arr(infer(ctx, s), s, schedules['BAC']))
    # The two prefixes are exactly the two sides of one substituted inner square.
    update_b = comp2(ctx, 0, src(ctx, src(ctx, a)), b)
    update_a = comp2(ctx, 0, a, tgt(ctx, src(ctx, b)))
    prefixes = temporal_words(ctx, update_b, update_a, 1, 2)
    for word, prefix in zip(('BAC', 'ABC'), prefixes, strict=True):
        assert comp2(ctx, 2, prefix, steps_by_word[word][2]) == schedules[word]
    assert steps_by_word['BAC'][2] == steps_by_word['ABC'][2]
    upper = susp_ctx(ctx)
    u, w = susp_tm(s), susp_tm(t)
    emitter.checks.append(f'shiftedJoinSupport : cohCase {emitter.ctx(upper)} {emitter.ty(infer(upper, u))} '
                          f'{emitter.tm(u)} {emitter.tm(w)} ≡ true\nshiftedJoinSupport = refl\n')

    def prism_at(data, inputs):
        shape, comparison = data
        return subst_tm(comparison, sub_from(shape, ctx, dict(zip(maximal_vars(shape), inputs, strict=True))))

    def inner(first, second, reverse):
        shape = tree_ctx(glue_tree(3, 1, 3))
        p, q = maximal_vars(shape)
        x, y = temporal_words(shape, v(p), v(q), 1, 2)
        change = head(shape, x, y) if reverse else head(shape, y, x)
        return subst_tm(change, sub_from(shape, ctx, {p: first, q: second}))

    def with_prefix(before, after, step):
        l = reassociate(ctx, steps_by_word[before], False)
        r = reassociate(ctx, steps_by_word[after], True)
        placed = comp2(ctx, 2, steps_by_word[before][0], step)
        return comp2(ctx, 3, comp2(ctx, 3, l, placed), r)

    # Both Gray routes reach ACB. The lower uses the reversed inner square.
    bc = prism_at(right_prism, (src(ctx, a), b))
    top1 = comp2(ctx, 2, bc, steps_by_word['BCA'][2])
    post_a = comp2(ctx, 0, a, src(ctx, src(ctx, b)))
    post_b = comp2(ctx, 0, tgt(ctx, src(ctx, a)), b)
    top2 = with_prefix('CBA', 'CAB', inner(post_a, post_b, False))
    ca = prism_at(left_prism, (a, src(ctx, b)))
    top3 = comp2(ctx, 2, ca, steps_by_word['CAB'][2])
    top = comp2(ctx, 3, comp2(ctx, 3, top1, top2), top3)
    lower2 = comp2(ctx, 2, inner(update_b, update_a, True), steps_by_word['BAC'][2])
    lower3 = with_prefix('ABC', 'ACB', prism_at(right_prism, (tgt(ctx, a), b)))
    lower = comp2(ctx, 3, comp2(ctx, 3, fitted, lower2), lower3)
    boundary = arr(infer(ctx, s), s, schedules['ACB'])
    for label, route in [('upperRoute', top), ('lowerRoute', lower)]:
        emitter.check_type(label, ctx, route, boundary)
    emitter.check_type('tensorAtom', ctx, head(ctx, top, lower), arr(boundary, top, lower))


def shorten(walk):
    """Return positions of the retained edges and the monotone map on vertices."""
    edges, projection = [], []
    pos = 0
    while pos < len(walk):
        last = max(i for i in range(pos, len(walk)) if walk[i] == walk[pos])
        projection.extend([len(edges)] * (last - pos + 1))
        if last + 1 < len(walk):
            edges.append(last)
        pos = last + 1
    return edges, projection


def chart(left_edges, right_edges):
    return tree_ctx((((chain_tree(left_edges),), (chain_tree(right_edges),)),))


def check_clamp(left, right, emitter):
    walks = (left, right)
    cuts = [shorten(w) for w in walks]
    large = chart(*(len(w) - 1 for w in walks))
    small = chart(*(len(edges) for edges, _ in cuts))

    def versions(ctx, left_count):
        slots = [i for i, ty in enumerate(ctx) if tdim(ty) + 1 == 3]
        return slots[:left_count], slots[left_count:]

    before = versions(large, len(left))
    after = versions(small, len(cuts[0][0]) + 1)
    moves = {ty[2][1]: v(i) for i, ty in enumerate(small) if tdim(ty) + 1 == 4}
    labels = {}
    for w, (edges, projection), old, new in zip(walks, cuts, before, after, strict=True):
        kept_states = [w[0]] + [w[i + 1] for i in edges]
        assert len(set(kept_states)) == len(kept_states)
        assert kept_states[-1] == w[-1]
        for i, (p, q) in enumerate(zip(projection, projection[1:])):
            if p != q:
                assert (w[i], w[i + 1]) == tuple(kept_states[p:q + 1])
        for pos, slot in enumerate(old):
            labels[slot] = v(new[projection[pos]])
    for i, ty in enumerate(large):
        if tdim(ty) + 1 == 4:
            s, t = (labels[side[1]] for side in ty[2:])
            labels[i] = identity(small, s) if s == t else moves[s[1]]
    clamp = sub_from(large, small, {i: labels[i] for i in maximal_vars(large)})
    assert all(infer(small, t) == subst_ty(a, clamp) for t, a in zip(clamp, large, strict=True))
    for endpoint in (0, -1):
        def layers(ctx, slots):
            return temporal_words(ctx, *(v(side[endpoint]) for side in slots), 1, 2)
        assert tuple(subst_tm(t, clamp) for t in layers(large, before)) == layers(small, after)
    if emitter:
        s, l, sub = emitter.ctx(small), emitter.ctx(large), emitter.sub(clamp)
        emitter.checks.append(f'eraseLoops : {s} ⊢sub {sub} ∶ {l}\n'
                              f'eraseLoops = from-just (checkSub {s} (from-just (checkCtx {s})) {sub} {l})\n')


def check_factor_projections():
    disk = tree_ctx(disc_tree(2))
    disk_atom = Complex(disk).atom(len(disk) - 1)
    count = 0
    for size in range(2, 6):
        for tree in trees(size):
            ctx = tree_ctx(tree)
            table = Complex(ctx)
            for index, dim in enumerate(table.deg):
                if dim == 2:
                    kept = support(table, table.atom(index))
                    residual, clamp = check_retraction(ctx, kept)
                    assert residual == disk
                    total = subst_tm(ucomp(ctx), clamp)
                    assert image_to_cell(strict_image(disk, total)) == raise_to(disk_atom, table.n)
                    count += 1
    return count


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    left_prism = check_prism(True, emitter)
    right_prism = check_prism(False, emitter)
    check_missing_join(emitter, left_prism, right_prism)
    walks = [(0,) + tail for n in range(4) for tail in product(range(2), repeat=n)]
    for left, right in product(walks, repeat=2):
        check_clamp(left, right, None)
    check_clamp((0, 1, 0, 2), (0, 1, 2, 1), emitter)
    factors = check_factor_projections()
    print(f'Checked both prisms, six schedules, {len(walks) ** 2 + 1} two-position contractions, '
          f'and {factors} projections of a column total.')
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = 'RealizedFour'
        source = emitter.module(module, __doc__)
        (args.agda_dir / (module + '.agda')).write_text(
            source.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))


if __name__ == '__main__':
    main()
