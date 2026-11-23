"""Check the single-edge component test and the ordinary product at repeated poles."""
from argparse import ArgumentParser
from functools import cache
from itertools import product
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, fv_ty, infer, subst_tm, subst_ty,
                  v)
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_path_lift import columns


def components(ctx):
    """Partition positive names by dependencies and test both spatial ends."""
    names = {i for i, ty in enumerate(ctx) if ty != STAR}
    adjacent = {i: set() for i in names}
    for i in names:
        for j in fv_ty(ctx[i]) & names:
            adjacent[i].add(j)
            adjacent[j].add(i)

    @cache
    def length(edge_term):
        if edge_term[0] == 'v':
            return 1
        return sum(length(edge_term[3][i]) for i in columns(edge_term[1])[1])

    def single(i):
        ty = ctx[i]
        if ty[1] == STAR:
            return True
        while ty[1][1] != STAR:
            ty = ty[1]
        return all(length(t) == 1 for t in ty[2:])

    pieces = []
    while names:
        todo = [min(names)]
        piece = set()
        while todo:
            i = todo.pop()
            if i not in piece:
                piece.add(i)
                todo.extend(adjacent[i] - piece)
        names -= piece
        pieces.append((piece, all(single(i) for i in piece)))
    return pieces


def build(length):
    # length=None folds the endpoints and both marker occurrences to one loop.
    count = 1 if length is None else length + 1
    ctx = [STAR] * count
    blocks = []

    def add(block, ty):
        block.append(v(len(ctx)))
        ctx.append(ty)
        return block[-1]

    for i in range(count):
        block = []
        unit = identity(tuple(ctx), v(i))
        a = add(block, arr(infer(tuple(ctx), unit), unit, unit))
        aa = comp2(tuple(ctx), 1, a, a)
        add(block, arr(infer(tuple(ctx), a), a, aa))
        blocks.append(block)
    for i in range(1 if length is None else length):
        block = []
        f = add(block, arr(STAR, v(i), v(0 if length is None else i + 1)))
        x = add(block, arr(infer(tuple(ctx), f), f, f))
        xx = comp2(tuple(ctx), 1, x, x)
        add(block, arr(infer(tuple(ctx), x), xx, x))
        blocks.append(block)
    check_ctx(tuple(ctx))
    return tuple(ctx), blocks


def check_terms(em, length):
    ctx, blocks = build(length)
    base, old = build(None)
    assert components(base) == [({t[1] for t in old[0]}, False),
                                ({t[1] for t in old[1]}, True)]
    # A declaration mixing a scalar at an empty path with the marked edge
    # joins the components, even though that declaration has one-edge ends.
    f = old[1][0]
    unit_f = comp2(base, 0, identity(base, v(0)), f)
    spatial = comp2(base, 0, old[0][0], f)
    mix = arr(infer(base, spatial), spatial, identity(base, unit_f))
    mixed = base + (mix,)
    check_ctx(mixed)
    assert components(mixed) == [(set(range(1, len(mixed))), False)]
    fold = [v(0)] * (length + 1)
    for j in range(len(blocks)):
        fold.extend(old[int(j > length)])
    fold = tuple(fold)
    word = []
    for i in range(length + 1):
        word.append(blocks[i][-1])
        if i < length:
            word.append(blocks[length + 1 + i][-1])
    joint = word[0]
    for t in word[1:]:
        joint = comp2(ctx, 0, joint, t)

    @cache
    def word_length(t):
        if t[0] == 'v':
            return int(t in old[1])
        return sum(word_length(t[3][i]) for i in columns(t[1])[1])

    def lift(t, p, q):
        if t[0] == 'v':
            if t == v(0):
                assert p == q
                return v(p)
            marked = int(t in old[1])
            assert q - p == marked
            return blocks[p + (length + 1 if marked else 0)][old[marked].index(t)]
        slots, edges = columns(t[1])
        ends = [p]
        for i in edges:
            ends.append(ends[-1] + word_length(t[3][i]))
        assert ends[-1] == q
        labels = tuple(lift(a, ends[slots[i]], ends[slots[i] + (t[1][i] != STAR)])
                       for i, a in enumerate(t[3]))
        return ('coh', t[1], t[2], labels)

    old_joint = subst_tm(joint, fold)
    assert lift(old_joint, 0, length) == joint
    em.check_type(f'word{length}', base, old_joint, subst_ty(infer(ctx, joint), fold))
    # Project the actual term with its literal, unit-padded boundary to each factor.
    gap, gap_blocks = build(0)
    marked_prefix, marked_blocks = build(1)
    # Restrict the two-pole chart to its crossing declarations.
    marker = [STAR, STAR]
    rename = [v(0), v(1)] + [v(0)] * (len(marked_prefix) - 2)
    marker_names = []
    for t in marked_blocks[-1]:
        ty = subst_ty(marked_prefix[t[1]], tuple(rename))
        name = v(len(marker))
        marker.append(ty)
        rename[t[1]] = name
        marker_names.append(name)
    marker = tuple(marker)
    check_ctx(marker)
    for focus, block in enumerate(blocks):
        crossing = focus > length
        target, names = (marker, marker_names) if crossing else (gap, gap_blocks[0])
        selected = {t[1]: name for t, name in zip(block, names)}
        boundary = focus - length if crossing else 0
        sigma = []
        for i, ty in enumerate(ctx):
            image_ty = subst_ty(ty, tuple(sigma))
            if ty == STAR:
                image = v(int(crossing and i >= boundary))
            elif i in selected:
                image = selected[i]
            else:
                origin = ty
                while origin[1] != STAR:
                    origin = origin[1]
                pole = sigma[origin[2][1]]
                point_ty = subst_ty(image_ty, (v(0),) * len(target))
                image = ('coh', (STAR,), point_ty, (pole,))
            assert infer(target, image) == image_ty
            sigma.append(image)
        t = subst_tm(joint, tuple(sigma))
        em.check_type(f'component{length}at{focus}', target, t, subst_ty(infer(ctx, joint), tuple(sigma)))
    return len(blocks)



def check_reachability(limit):
    # The base creates a loop on an empty edge path and merges two loops.
    # The marked component changes P to Q. Costs count generating steps.
    base_rules = [('', 'a'), ('aa', 'b')]
    marked_rules = [('P', 'Q')]

    def distances(start, rules):
        result = {start: 0}
        frontier = {start}
        for cost in range(1, limit + 1):
            following = {word[:i] + new + word[i + len(old):]
                         for word in frontier for old, new in rules
                         for i in range(len(word) + 1) if word.startswith(old, i)}
            frontier = following - result.keys()
            result.update((word, cost) for word in frontier)
        return result

    cases = 0
    for visits in range(4):
        for gaps in product(('', 'a'), repeat=visits + 1):
            parts = [gaps[0]]
            for gap in gaps[1:]:
                parts.extend(('P', gap))
            local = [distances(part, marked_rules if i % 2 else base_rules)
                     for i, part in enumerate(parts)]
            expected = {}
            for factors in product(*(table.items() for table in local)):
                words, costs = zip(*factors)
                if sum(costs) <= limit:
                    expected[''.join(words)] = sum(costs)
            actual = distances(''.join(parts), base_rules + marked_rules)
            assert expected == actual
            cases += len(actual)
    return cases


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    print('Bounded endpoint distances:', check_reachability(4))
    em = Emitter()
    print('Independent positions per word:', [check_terms(em, k) for k in (0, 1, 2, 3)])
    if args.agda_dir:
        name = 'OrdinaryEdgeComponents'
        (args.agda_dir / (name + '.agda')).write_text(em.module(name, __doc__))
