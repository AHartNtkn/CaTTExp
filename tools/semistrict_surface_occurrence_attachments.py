"""Compute pushouts of written occurrence diagrams along attaching faces."""
from argparse import ArgumentParser
from collections import deque
from itertools import product
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, infer, maximal_vars, src,
                  sub_from, subst_tm, subst_ty, tdim, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_occurrence_computads import maps_over, unfold


def pushout(left, left_fold, right, right_fold, a, b):
    """Identify a(i) on the left with b(i) on the right, allowing repetitions."""
    offset = len(left)
    shift = tuple(v(offset + i) for i in range(len(right)))
    types = left + tuple(subst_ty(ty, shift) for ty in right)
    labels = left_fold + right_fold
    parent = list(range(len(types)))

    def root(i):
        while i != parent[i]:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for x, y in zip(a, b, strict=True):
        i, j = root(x[1]), root(offset + y[1])
        assert labels[i] == labels[j]
        parent[j] = i
    reps = sorted({root(i) for i in parent}, key=lambda i: (tdim(types[i]), i))
    numbering = {i: v(k) for k, i in enumerate(reps)}
    quotient = tuple(numbering[root(i)] for i in range(len(types)))
    shape = tuple(subst_ty(types[i], quotient) for i in reps)
    for i, image in enumerate(quotient):
        assert shape[image[1]] == subst_ty(types[i], quotient)
    check_ctx(shape)
    return shape, tuple(labels[i] for i in reps), quotient[:offset], quotient[offset:]


def cuts(ctx):
    vertices = [i for i, ty in enumerate(ctx) if ty == STAR]
    results = []
    for values in product((0, 1), repeat=len(vertices)):
        colours = dict(zip(vertices, values, strict=True))
        for i, ty in enumerate(ctx):
            if ty == STAR:
                continue
            rank = tdim(ty) + 1
            s, t = v(i), v(i)
            for _ in range(rank):
                s, t = src(ctx, s), tgt(ctx, t)
            a, b = colours[s[1]], colours[t[1]]
            if a > b or (rank >= 2 and (a, b) != (0, 1)):
                break
        else:
            results.append(colours)
    return results


def three_edges():
    ctx = (STAR, arr(STAR, v(0), v(0)))
    f = v(1)
    ff = comp2(ctx, 0, f, f)
    path = comp2(ctx, 0, ff, f)
    ctx += (arr(infer(ctx, ff), ff, ff),)
    h = v(2)
    line = tree_ctx(string_tree(0, [1, 1, 1]))
    slots = maximal_vars(line)
    a, b, c = map(v, slots)
    l = comp2(line, 0, comp2(line, 0, a, b), c)
    r = comp2(line, 0, a, comp2(line, 0, b, c))
    sig = sub_from(line, ctx, dict.fromkeys(slots, f))
    change = subst_tm(head(line, l, r), sig)
    back = subst_tm(head(line, r, l), sig)
    left = comp2(ctx, 0, h, f)
    right = composite(ctx, 1, (change, comp2(ctx, 0, f, h), back))
    empty = identity(ctx, path)
    excursions = []
    for gate in (left, right):
        assert infer(ctx, gate) == infer(ctx, empty)
        birth, death = v(len(ctx)), v(len(ctx) + 1)
        ctx += (arr(infer(ctx, empty), empty, gate), arr(infer(ctx, empty), gate, empty))
        excursions.append(comp2(ctx, 2, birth, death))
    left_bubble, right_bubble = excursions
    return ctx, left_bubble, right_bubble


def face_map(face, diagram, lifted_face):
    source, value, source_fold = face
    upper, _, upper_fold = diagram
    matches = [m for m in maps_over(source, source_fold, upper, upper_fold)
               if subst_tm(value, m) == lifted_face]
    assert len(matches) == 1
    return matches[0]


def cut_ports(ctx, term):
    while tdim(infer(ctx, term)) > 0:
        term = src(ctx, term)
    path = edges(term)
    return {tuple((colours[src(ctx, f)[1]], colours[tgt(ctx, f)[1]]) for f in path).index((0, 1)) + 1
            for colours in cuts(ctx)}


def edges(term):
    if term[0] == 'v':
        return [term]
    return [f for arg, ty in zip(term[3], term[1], strict=True) if tdim(ty) == 0 for f in edges(arg)]


def test_ports(emitter):
    ctx, s, t = three_edges()
    g = v(len(ctx))
    ctx += (arr(infer(ctx, s), s, t),)
    source, target, rule = (unfold(ctx, term) for term in (s, t, g))
    for diagram, expected in ((source, {1, 2}), (target, {2, 3}), (rule, {2})):
        shape, term, _ = diagram
        assert cut_ports(shape, term) == expected
    inclusion = face_map(source, rule, src(rule[0], rule[1]))
    written = comp2(ctx, 2, s, s)
    old_target = comp2(ctx, 2, t, t)
    start, initial, fold = unfold(ctx, written)
    states = [(start, fold, initial, [])]
    for _ in range(2):
        new = []
        for shape, labels, first, rules in states:
            for match in maps_over(source[0], source[2], shape, labels):
                up, up_fold, prev, fresh = pushout(shape, labels, rule[0], rule[2], match, inclusion)
                new.append((up, up_fold, subst_tm(first, prev),
                            [subst_tm(z, prev) for z in rules] + [subst_tm(rule[1], fresh)]))
        states = new
    assert len(states) == 4
    successes = 0
    for shape, labels, first, rules in states:
        assert cut_ports(shape, first) == {2}
        z, w = rules
        # Apply z to the first operand and w to the second. Selecting the
        # same source occurrence twice still gives a legal diagram pushout.
        if first != comp2(shape, 2, src(shape, z), src(shape, w)):
            continue
        witness = comp2(shape, 3, comp2(shape, 2, z, src(shape, w)),
                        comp2(shape, 2, tgt(shape, z), w))
        end = tgt(shape, witness)
        assert src(shape, witness) == first
        assert subst_tm(end, labels) == old_target
        original = comp2(ctx, 3, comp2(ctx, 2, g, s), comp2(ctx, 2, t, g))
        emitter.check_type('twoUses', shape, witness, arr(infer(shape, first), first, end))
        emitter.check_eq('foldTwoUses', witness, labels, original)
        direct, universal, direct_fold = unfold(ctx, original)
        iso = face_map((direct, universal, direct_fold), (shape, witness, labels), witness)
        assert len(direct) == len(shape) == len(set(iso))
        successes += 1
    assert successes == 1
    print('Source ports 1,2; target ports 2,3; rule port 2. All four two-step diagrams admit the middle cut.')


def compress(shape, fold, initial):
    """Retain vertices and identify higher generators at equal labelled types."""
    types, labels = [], []
    images = [None] * len(shape)
    for rank in sorted({tdim(ty) + 1 for ty in shape}):
        groups = {}
        for i, ty in enumerate(shape):
            if tdim(ty) + 1 == rank:
                key = (fold[i], subst_ty(ty, images), i if rank == 0 else 0)
                groups.setdefault(key, []).append(i)
        for (label, ty, _), group in sorted(groups.items()):
            for i in group:
                images[i] = v(len(types))
            labels.append(label)
            types.append(ty)
    ctx = tuple(types)
    check_ctx(ctx)
    return ctx, tuple(labels), subst_tm(initial, images)


def check_unbounded(emitter):
    ctx, left, right = three_edges()
    f = v(1)
    a = v(len(ctx))
    ctx += (arr(infer(ctx, f), f, f),)
    middle = comp2(ctx, 0, comp2(ctx, 0, f, a), f)
    empty = src(ctx, left)
    birth, death = v(len(ctx)), v(len(ctx) + 1)
    ctx += (arr(infer(ctx, empty), empty, middle), arr(infer(ctx, empty), middle, empty))
    marked = comp2(ctx, 2, birth, death)
    pair = comp2(ctx, 2, right, right)
    expand, contract = v(len(ctx)), v(len(ctx) + 1)
    ctx += (arr(infer(ctx, left), left, pair), arr(infer(ctx, left), pair, left))
    initial = comp2(ctx, 2, marked, left)
    target = comp2(ctx, 2, marked, pair)
    templates = []
    for term in (expand, contract):
        rule = unfold(ctx, term)
        source = unfold(ctx, src(ctx, term))
        inc = face_map(source, rule, src(rule[0], rule[1]))
        vertices = {v(i) for i, ty in enumerate(rule[0]) if ty == STAR}
        assert vertices <= set(inc)
        templates.append((source, rule, inc))
    shape, value, fold = unfold(ctx, initial)
    first = compress(shape, fold, value)
    todo, seen = deque([first]), {first}
    target_ctx, target_term, target_fold = unfold(ctx, target)
    transitions = terminal_states = 0
    while todo:
        shape, fold, value = todo.popleft()
        assert sum(ty == STAR for ty in shape) == 4
        assert sum(tdim(ty) == 0 for ty in shape) == 3
        assert cut_ports(shape, value) == {2}
        lifts = (subst_tm(target_term, m) for m in maps_over(target_ctx, target_fold, shape, fold))
        if any(infer(shape, end) == infer(shape, value) for end in lifts):
            terminal_states += 1
        for source, rule, inc in templates:
            for m in maps_over(source[0], source[2], shape, fold):
                new, labels, prev, _ = pushout(shape, fold, rule[0], rule[2], m, inc)
                state = compress(new, labels, subst_tm(value, prev))
                transitions += 1
                if state not in seen:
                    seen.add(state)
                    todo.append(state)
    assert (len(seen), transitions, terminal_states) == (3, 5, 2)
    forward = comp2(ctx, 2, marked, expand)
    reverse = comp2(ctx, 2, marked, contract)
    assert (src(ctx, forward), tgt(ctx, forward)) == (initial, target)
    loop = comp2(ctx, 3, forward, reverse)
    emitter.check_type('repeat', ctx, loop, arr(infer(ctx, initial), initial, initial))
    print('Expansion/contraction: 3 cut presentations, 5 transitions, 2 states supporting the written target.')


def test_identification():
    # A 2-generator f => 1_x identifies the two *occurrences* of x on f.
    base = (STAR, arr(STAR, v(0), v(0)))
    f = v(1)
    base += (arr(infer(base, f), f, identity(base, v(0))),)
    source, rule = unfold(base, f), unfold(base, v(2))
    inc = face_map(source, rule, src(rule[0], rule[1]))
    path = comp2(base, 0, f, f)
    shape, term, fold = unfold(base, path)
    candidates = list(maps_over(source[0], source[2], shape, fold))
    assert len(candidates) == 2
    for match in candidates:
        result, _, prev, _ = pushout(shape, fold, rule[0], rule[2], match, inc)
        assert sum(ty == STAR for ty in result) == 2
        assert len(set(prev)) + 1 == len(prev)
        assert len(edges(subst_tm(term, prev))) == 2
    print('Both attachments of f => 1_x to the two-edge source identify exactly one pair of vertices.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    test_identification()
    test_ports(emitter)
    check_unbounded(emitter)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('OccurrenceAttachments', __doc__).replace('open import CaTTExp.Pure',
                                                                         'open import CaTTExp.Gray.Pure')
        (args.agda_dir / 'OccurrenceAttachments.agda').write_text(module)
