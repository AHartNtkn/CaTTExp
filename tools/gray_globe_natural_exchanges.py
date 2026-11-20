"""Check pure naturality exchanges and the mixed tests for the word presentation at (3,3)."""
import argparse
from collections import Counter
from itertools import permutations
from pathlib import Path

from canonical_gray_two_discs import tableau_interpreter
from catt import STAR, arr, check_ctx, comp2, infer, maximal_vars, src, tgt, tree_ctx, v
from emit_agda import Emitter
from gray_globe_attachments import ordered_factors
from gray_globe_boundary_fibres import sort_face_patches
from gray_globe_comparison import atom, face
from gray_globe_corner_prisms import fold
from gray_globe_exterior_actions import arity, coherence
from gray_globe_factorizations import orders, profile, rank
from gray_globe_pure_extension import raise_argument
from gray_globe_section import EMPTY_ROW, cells, row_map
from gray_globe_strip_squares import lift_on, minimal_shape
from gray_path_wedge import compose


def top_sites(w):
    return tuple(map(rank, w[-1][0]))


def word(w):
    return ordered_factors(w, len(w)-2, {p: p[0] for p in top_sites(w)})


def central_word(z):
    owner = {p: p[0] for p in top_sites(z)}
    before = orders(z, 4, owner)
    if not {(2, 1), (2, 3), (4, 3)} <= before:
        return word(z)
    required = before | {(4, 1)}
    priority = next(seq for seq in permutations(sorted(owner.values()))
                    if all(seq.index(a) < seq.index(b) for a, b in required))
    return ordered_factors(z, 4, {p: priority.index(i) for p, i in owner.items()})


def outer_relations(z):
    sites = top_sites(z)
    if not {1, 2, 3, 4} <= {q[0] for q in sites}:
        return None
    before = orders(z, 4, {q: q[0] for q in sites})
    return (1, 2) in before, (3, 4) in before


def chord_order(w, owner, precedence):
    """Sort each consecutive run separately, with one extra order inside the mixed run."""
    before = orders(w, 4, owner)
    if precedence is not None:
        a, b = (1, 4) if precedence else (4, 1)
        before.add((owner[a, 5-a], owner[b, 5-b]))
    # Give each group its true left index, including the active two-letter group.
    left = {group: min(i for (i, j), g in owner.items() if g == group and i+j == 5)
            for group in owner.values()}
    pending = set(left)
    priority = {}
    while pending:
        available = (g for g in pending if not any(a in pending and b == g for a, b in before))
        g = min(available, key=left.__getitem__)
        priority[g] = len(priority)
        pending.remove(g)
    return ordered_factors(w, 4, {q: priority[g] for q, g in owner.items()})


def layer_word(z):
    outer = outer_relations(z)
    return chord_order(z, {q: q[0] for q in top_sites(z)}, outer[0] if outer else None)


def layer_blocks(w, owner):
    sides = [outer_relations(face(w, k)) for k in (0, 1)]
    if sides == [None, None]:
        return chord_order(w, owner, None)
    # A face with equal exterior orientations prescribes the order of 1 and 4.
    fixed = {a for a, b in sides if a == b}
    assert len(fixed) <= 1
    desired = next(iter(fixed)) if fixed else sides[0][0]
    return chord_order(w, owner, desired)


def check_forced_outer_swaps(expected):
    domain = cells((4, 4)) - {()}
    run = ((1, 4), (2, 3), (3, 2), (4, 1))
    vertices = {}
    for z in domain:
        if top_sites(z) == run:
            before = orders(z, 4, {q: q[0] for q in run})
            key = tuple(int((i+1, i) in before) for i in (1, 2, 3))
            assert key not in vertices
            vertices[key] = z
    edges = {(face(w, 0), face(w, 1)) for w in domain if len(w) == 7 and len(top_sites(w)) == 1}
    found = set()
    for first, second in [((0, 0, 1), (0, 1, 1)), ((1, 0, 0), (1, 1, 0))]:
        path = [vertices[key] for key in ((0, 0, 0), first, second, (1, 1, 1))]
        assert all((a, b) in edges for a, b in zip(path, path[1:]))
        patches = set()
        for z in path[1:3]:
            before = orders(z, 4, {q: q[0] for q in run})
            for seq in permutations(range(1, 5)):
                if abs(seq.index(1)-seq.index(4)) != 1 or any(seq.index(a)>seq.index(b) for a, b in before):
                    continue
                i = min(seq.index(1), seq.index(4))
                assert i == (2 if first[0] else 0)
                parts = ordered_factors(z, 4, {q: seq.index(q[0]) for q in run})
                patches.add(compose(*parts[i:i+2], 4))
        patch, = patches
        # In the spatial cut the (2,2) factor separates the two active blocks.
        owner = {q: 0 if q[0] <= 1 else 1 if q == (2, 2) else 2 for q in profile(patch) if sum(q) > 3}
        assert orders(patch, 3, owner) in ({(0, 1), (1, 2)}, {(2, 1), (1, 0)})
        found.add(patch)
    assert len(vertices) == 8 and found == expected


def check_pure_squares(domain):
    count = 0
    for w in domain:
        d = len(w)-1
        sites = top_sites(w)
        if len(sites) != 2 or sites[1][0]-sites[0][0] < 2:
            continue
        for g in w[-1][0]:
            p = rank(g)
            if min(p):
                continue
            pure_first, step_plus = ordered_factors(w, d-1, {q: int(q != p) for q in sites})
            step_minus, pure_last = ordered_factors(w, d-1, {q: int(q == p) for q in sites})
            x, = atom(g)[d-1][0]
            y, = atom(g)[d-1][1]
            replace = lambda h: y if h == x else h
            assert row_map(step_minus, 0, replace) == step_plus
            assert all(x in chain for chain in step_minus[d-1])
            assert x not in {h for pair in atom(step_minus[-1][0][0]) for chain in pair for h in chain}
            for pure, side in ((pure_first, 0), (pure_last, 1)):
                assert pure[-1][0] == (g,)
                assert face(pure, 0) == face(step_minus, side)
                assert face(pure, 1) == face(step_plus, side)
            count += 1
    return count


def pure_tree(w, axes):
    """The actual nested cut-three decomposition; the only higher site on a peeled axis is pure four."""
    if not axes:
        return w
    axis, *rest = axes
    ranks = profile(w)
    outside = {p for p in ranks if p[axis] > 3}
    if not outside:
        return pure_tree(w, rest)
    assert outside == {((4, 0), (0, 4))[axis]}
    parts = ordered_factors(w, 3, {p: int(p in outside) for p in ranks if sum(p) > 3})
    if len(parts) == 1:
        assert len(w) == 5 and top_sites(w) == tuple(outside)
        return w
    return [c if outside & profile(c) else pure_tree(c, rest) for c in parts]


def leaves(tree):
    if isinstance(tree, list):
        return [c for child in tree for c in leaves(child)]
    return [tree]


def compose_tree(tree, leaf, ctx):
    if isinstance(tree, list):
        a, b = (compose_tree(child, leaf, ctx) for child in tree)
        return comp2(ctx(), 3, a, b)
    return leaf(tree)


def string_tree(heights):
    # Each spatial factor is either one 4-globe or a cut-four string of 5-globes.
    tree = tuple(tuple(() for _ in range(k)) for k in heights)
    for _ in range(3):
        tree = (tree,)
    return tree_ctx(tree)


def check_short(w, emitter):
    """Specialize the two distributors and paste a 6-term at the actual word boundaries."""
    variables, ctx = {}, ()
    def declare(c):
        nonlocal ctx
        if c not in variables:
            if len(c) == 1:
                ty = STAR
            elif len(c) == 7:
                s, t = (native(face(c, side)) for side in (0, 1))
                ty = arr(infer(ctx, s), s, t)
            else:
                s, t = (declare(face(c, side)) for side in (0, 1))
                ty = arr(infer(ctx, s), s, t)
            variables[c] = v(len(ctx))
            ctx += (ty,)
        return variables[c]

    def native(c):
        if len(c) == 6:
            args = [declare(f) for f in word(c)]
            return fold(ctx, 4, args)
        return declare(c)

    axes = (0, 1)
    def raw(c):
        return compose_tree(pure_tree(c, axes), native, lambda: ctx)

    middle = raw(w)
    ends, changes = [], []
    for side in (0, 1):
        z = face(w, side)
        steps = [raw(c) for c in word(z)]
        chosen = fold(ctx, 4, steps)
        old = raw(z)
        assert (src, tgt)[side](ctx, middle) == old
        ends.append(chosen)
        if old == chosen:
            changes.append(None)
            continue
        slots, heights = [], []
        for c in leaves(pure_tree(z, axes)):
            args = word(c) if len(c) == 6 else (c,)
            heights.append(len(args) if len(c) == 6 else 0)
            slots.extend(declare(a) for a in args)
        s, t = (old, chosen) if side else (chosen, old)
        changes.append(lift_on(ctx, string_tree(heights), slots, s, t))
    term = fold(ctx, 5, [t for t in (changes[0], middle, changes[1]) if t is not None])
    wanted = arr(infer(ctx, ends[0]), *ends)
    check_ctx(ctx)
    assert infer(ctx, term) == wanted
    labels = tuple(variables)
    evaluate = tableau_interpreter(ctx, labels.__getitem__)
    assert evaluate(term) == w and all(evaluate(t) == face(w, i) for i, t in enumerate(ends))
    if emitter:
        emitter.check_type('central-word-lift', ctx, term, wanted)


def generic_squares(emitter):
    """The literal raised pure terms, and the exchange with a common stationary comparison."""
    ctx = arity(3, (5, 5))
    slots = [v(i) for i in maximal_vars(ctx)]
    for index in (0, 1):
        marked, moving = slots[index], slots[1-index]
        x = src(ctx, marked)
        def paste(a, b):
            return comp2(ctx, 3, a, b) if index == 0 else comp2(ctx, 3, b, a)
        pure = [raise_argument(ctx, paste(x, f(ctx, moving)), x, marked) for f in (src, tgt)]
        lower = comp2(ctx, 4, paste(x, moving), pure[1])
        upper = comp2(ctx, 4, pure[0], paste(tgt(ctx, marked), moving))
        for name, s, t in [('pure', lower, upper), ('pure-inverse', upper, lower)]:
            want = arr(infer(ctx, s), s, t)
            term = coherence(ctx, s, t)
            assert infer(ctx, term) == want
            if emitter:
                emitter.check_type(f'{name}-{index}', ctx, term, want)
    a, b = (v(i) for i in maximal_vars(ctx))
    first = comp2(ctx, 4, comp2(ctx, 3, a, src(ctx, b)), comp2(ctx, 3, tgt(ctx, a), b))
    second = comp2(ctx, 4, comp2(ctx, 3, src(ctx, a), b), comp2(ctx, 3, a, tgt(ctx, b)))
    term = coherence(ctx, first, second)
    assert infer(ctx, term) == arr(infer(ctx, first), first, second)
    if emitter:
        emitter.check_type('native-and-pure-exchange', ctx, term, infer(ctx, term))


def check_bare(p, axis, emitter):
    """The two consecutive mixed blocks in each of the two native growth conventions."""
    def split(w, cut, cutoff):
        return ordered_factors(w, cut, {q: int(q[axis] > cutoff) for q in profile(w) if sum(q) > cut})

    pure3, pure4, edge3 = [(a, b) if axis else (b, a) for a, b in ((0, 3), (0, 4), (1, 3))]
    owner = {q: int(q[axis] >= 3) for q in profile(p) if sum(q) > 3}
    ordered = ordered_factors(p, 3, owner)
    reversed_blocks = top_sites(ordered[0])[0][axis] == 4
    direction = 'exterior-first' if reversed_blocks else 'central-first'
    def native_order(a, b):
        return (b, a) if reversed_blocks else (a, b)

    P, E = native_order(*ordered)
    assert top_sites(P)[0][axis] == 2 and top_sites(E)[0][axis] == 4
    ctx, variables, chosen = (), {}, {}

    def parameter(c):
        nonlocal ctx
        if c not in variables:
            if len(c) == 1:
                ty = STAR
            else:
                s, t = (rep(face(c, side)) for side in (0, 1))
                ty = arr(infer(ctx, s), s, t)
            variables[c] = v(len(ctx))
            ctx += (ty,)
        return variables[c]

    def paste(cut, operands):
        args = [rep(c) for c in operands]
        return fold(ctx, cut, args)

    def rep(c):
        if c in chosen:
            return chosen[c]
        d = len(c)-1
        sites = profile(c)
        if d == 4 and top_sites(c) == (pure4,):
            parts = split(c, 2, 2)
            if len(parts) == 1:
                result = parameter(c)
            else:
                high, = [f for f in parts if len(f) == 5]
                base = rep(face(c, 0))
                moving = rep(high)
                result = raise_argument(ctx, base, src(ctx, moving), moving)
        elif d >= 4 and c != E and pure4 in sites:
            result = paste(3, split(c, 3, 3))
        elif d >= 4 and edge3 in sites and top_sites(c) != (edge3,) and c != E:
            result = paste(3, split(c, 3, 2))
        elif d >= 3 and pure3 in sites and edge3 not in sites and len(split(c, 2, 2)) > 1:
            result = paste(2, split(c, 2, 2))
        else:
            result = parameter(c)
        chosen[c] = result
        if d:
            ends = tuple(rep(face(c, s)) for s in (0, 1))
            assert infer(ctx, result)[2:] == ends
        return result

    # Inspect the native term in both temporal orders. The other spatial
    # factor is an existing edge lift at its prescribed boundaries.
    central, exterior = rep(P), rep(E)
    spatial = native_order(central, exterior)
    def mul(a, b):
        return comp2(ctx, 3, a, b)

    def product(a, b):
        return mul(*native_order(a, b))

    for first in top_sites(p):
        steps = ordered_factors(p, 4, {q: int(q != first) for q in top_sites(p)})
        u, = [w for w in steps if top_sites(w) == top_sites(P)]
        native, = [w for w in leaves(pure_tree(u, (axis,))) if len(w) == 6]
        Y, = [w for w in leaves(pure_tree(u, (axis,))) if len(w) == 5]
        Q, e = native_order(*split(native, 3, 2))
        assert top_sites(e) == (edge3,) and Q[-1] == P[-1]
        old = rep(u)
        qterm, eterm, yterm = (rep(c) for c in (Q, e, Y))
        side = int(first == top_sites(E)[0])
        if Q == P:
            assert old == product(product(qterm, eterm), yterm)
            assert (src, tgt)[side](ctx, exterior) == product(eterm, yterm)
            continue
        assert old == product(yterm, product(qterm, eterm))
        y_at_seam, e_at_seam = native_order(*split(face(E, side), 3, 3))
        assert e_at_seam == e and rep(face(E, side)) == product(rep(y_at_seam), eterm)
        # Both temporal orders of the local Y,Q change on the same cut-two tree.
        patch = compose(*native_order(Y+(EMPTY_ROW,), Q), 3)
        assert compose(*native_order(P, y_at_seam+(EMPTY_ROW,)), 3) == patch
        factors = split(patch, 2, 2)
        H, = [c for c in factors if len(c) == 5]
        G, = [c for c in factors if len(c) == 6]
        assert top_sites(H) == (pure4,) and G == atom(P[-1][0][0])
        slots = [rep(c) for c in factors]
        left = product(yterm, qterm)
        right = product(central, rep(y_at_seam))
        corner_changes = []
        for op in (src, tgt):
            s, t = op(ctx, left), op(ctx, right)
            reduced = [slot if c == H else op(ctx, slot) for c, slot in zip(factors, slots)]
            corner_changes.append(lift_on(ctx, arity(2, (4, 4)), reduced, s, t))
        s = comp2(ctx, 4, left, corner_changes[1])
        t = comp2(ctx, 4, corner_changes[0], right)
        active_square = lift_on(ctx, arity(2, tuple(len(c)-1 for c in factors)), slots, s, t)
        assert infer(ctx, active_square)[2:] == (s, t)
        values = tuple(variables)
        evaluate = tableau_interpreter(ctx, values.__getitem__)
        assert evaluate(s) == evaluate(t) == patch
        assert evaluate(active_square) == patch + (EMPTY_ROW,)
        if emitter:
            emitter.check_type(f'bare-native-square-{axis}-{direction}', ctx, active_square, infer(ctx, active_square))
    # The outer exchange has the two actual spatial terms as its slots.
    a, b = spatial
    forward = comp2(ctx, 4, mul(a, src(ctx, b)), mul(tgt(ctx, a), b))
    backward = comp2(ctx, 4, mul(src(ctx, a), b), mul(a, tgt(ctx, b)))
    exchange = lift_on(ctx, arity(3, (5, 5)), spatial, forward, backward)
    values = tuple(variables)
    evaluate = tableau_interpreter(ctx, values.__getitem__)
    assert evaluate(forward) == evaluate(backward) == p and evaluate(exchange) == p+(EMPTY_ROW,)
    if emitter:
        emitter.check_type(f'bare-outer-exchange-{axis}-{direction}', ctx, exchange, infer(ctx, exchange))


def check(m, n, emitter):
    domain = cells((m, n)) - {()}
    print('Pure-mark directed configurations:', check_pure_squares(domain))
    centres = {minimal_shape(w) for w in domain if top_sites(w) == ((3, 3),)}
    short = {w for w in centres if set(map(rank, w[5][0])) == {(2, 3), (3, 2)}}
    if min(m, n) < 5:
        return
    assert len(centres) == 121 and len(short) == 9
    example = next(w for w in sorted(short) if len(leaves(pure_tree(w, (0, 1)))) == 3)
    for w in short:
        check_short(w, emitter if w == example else None)

    all_patches = {w: set(sort_face_patches(w)) for w in centres}
    mixed = {p for patches in all_patches.values() for p in patches if all(min(q) for q in top_sites(p))}
    need = Counter(len(patches & mixed) for patches in all_patches.values())
    bases, changes = set(), Counter()
    near_sites = {((1, 4), (3, 2)), ((2, 3), (4, 1))}
    near = {minimal_shape(w) for w in domain if top_sites(w) in near_sites}
    assert len(near) == 12
    for patch in near | mixed:
        pair = tuple(p[0] for p in top_sites(patch))
        axes = {(1, 3): (0,), (2, 4): (1,), (1, 4): ()}[pair]
        parts = leaves(pure_tree(patch, axes))
        q, = [c for c in parts if len(c) == 6]
        if patch in mixed:
            bases.add(minimal_shape(q))
        if len(parts) > 1:
            for first in pair:
                alt = ordered_factors(patch, 4, {r: int(r[0] != first) for r in top_sites(patch)})
                base_steps = ordered_factors(q, 4, {r: int(r[0] != first) for r in top_sites(q)})
                for step, inside in zip(alt, base_steps):
                    assert leaves(pure_tree(step, axes)) == [inside if c == q else c for c in parts]
                    if top_sites(step) == ((2, 3),):
                        a, b = [leaves(pure_tree(step, order)) for order in ((0, 1), (1, 0))]
                        assert {len(a), len(b)} == {3}
                        assert next(c for c in a if len(c) == 6) == next(c for c in b if len(c) == 6)
                        if a != b:
                            heights = [len(c) for c in a]
                            assert heights == [len(c) for c in b] and heights in ([5, 5, 6], [6, 5, 5])
                            assert compose(*[c for c in a if len(c) == 5], 3) == compose(
                                *[c for c in b if len(c) == 5], 3)
                        changes['exchange' if a != b else 'rebracket'] += 1
    assert len(set.union(*all_patches.values())) == 37 and len(mixed) == 7 and len(bases) == 3
    for axis, sites in enumerate((((2, 3), (4, 1)), ((1, 4), (3, 2)))):
        pair = (4, 3) if axis == 0 else (3, 4)
        signed = {w for w in cells(pair) if w and top_sites(w) == sites}
        assert len(signed) == 2 and next(z for z in bases if top_sites(z) == sites) in signed
        incident = []
        for z in sorted(signed):
            check_bare(z, axis, emitter)
            incident.append({minimal_shape(c) for first in sites for c in ordered_factors(
                z, 4, {q: int(q != first) for q in sites})})
        assert len(incident[0]) == len(incident[1]) == 4 and incident[0].isdisjoint(incident[1])
    residual, = [z for z in bases if top_sites(z) == ((1, 4), (4, 1))]
    assert sum(residual not in patches for patches in all_patches.values()) == 112
    other_steps = set()
    for z in mixed - {residual}:
        for first in top_sites(z):
            other_steps.update(minimal_shape(c) for c in ordered_factors(
                z, 4, {q: int(q != first) for q in top_sites(z)}))
    for first in top_sites(residual):
        assert all(minimal_shape(c) in other_steps for c in ordered_factors(
            residual, 4, {q: int(q != first) for q in top_sites(residual)}))
    modified_faces = set()
    old_mixed_cases = 0
    for w, patches in all_patches.items():
        amended = set(sort_face_patches(w, central_word))
        assert residual not in amended and {p for p in amended if all(min(q) for q in top_sites(p))} <= mixed
        s, t = (face(w, j) for j in (0, 1))
        assert central_word(t) == word(t)
        if word(s) != central_word(s):
            assert residual in patches and s not in modified_faces
            left, right = [[top_sites(u)[0][0] for u in word(c)] for c in (s, t)]
            assert left.index(1) < left.index(4) and right.index(4) < right.index(1)
            modified_faces.add(s)
        if any(all(min(q) for q in top_sites(p)) for p in amended):
            old_mixed_cases += 1
    assert len(modified_faces) == 9
    print('Nine short word lifts; central inputs by number of mixed sorting patches:', dict(sorted(need.items())))
    print('Mixed patches after pure padding is stripped:', sorted(z[-1][0] for z in bases))
    print('Changes of axis order on central singletons:', dict(changes))
    print('Central inputs independent of the residual mixed exchange: 112 of 121')
    print('All 121 central word lifts use the proved exchanges after changing nine source words;',
          old_mixed_cases, 'use mixed exchanges')

    singles = {minimal_shape(w) for w in domain if len(w) == 7 and len(top_sites(w)) == 1}
    needed = set()
    by_site = Counter()
    for w in singles:
        mixed_patches = {p for p in sort_face_patches(w, layer_word, layer_blocks)
                         if all(min(q) for q in top_sites(p))}
        far = mixed_patches - near
        if far:
            assert top_sites(w) == ((2, 4),)
            by_site[top_sites(w)[0]] += 1
        needed.update(far)
    assert len(needed) == 2
    assert {tuple((g[0][1], g[1][1]) for g in z[-1][0]) for z in needed} == {
        ((0, 2), (2, 1)), ((1, 2), (2, 0))}
    assert all(top_sites(z) == ((1, 4), (4, 1)) and (2, 2) in profile(z) for z in needed)
    check_forced_outer_swaps(needed)
    print('Layer word checked on', len(singles), 'six-singleton shapes. Two remaining exchange shapes;',
          dict(by_site), 'inputs use them.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if min(args.m, args.n) < 0:
        parser.error('use nonnegative globe dimensions')
    emitter = Emitter() if args.agda else None
    generic_squares(emitter)
    check(args.m, args.n, emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Pure naturality and central word lifts.'))
