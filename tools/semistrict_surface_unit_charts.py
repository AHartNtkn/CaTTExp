"""Check the two counits of a unit chart and the empty-seam criterion on planar charts."""

from argparse import ArgumentParser
from collections import Counter
from itertools import product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, fv_ty, infer, subst_tm, subst_ty, v
from ct_suspension import susp_ctx, susp_tm, susp_ty
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity


def checked(labels, source, target):
    result = tuple(labels)
    assert len(result) == len(source)
    for ty, term in zip(source, result):
        assert subst_ty(ty, result) == infer(target, term)
    return result


def glue(first, second, shared):
    """Append the second computad with the prescribed generator identifications."""
    context = list(first)
    labels = []
    for i, ty in enumerate(second):
        actual = subst_ty(ty, labels)
        if i in shared:
            label = shared[i]
            assert context[label[1]] == actual
        else:
            label = v(len(context))
            context.append(actual)
        labels.append(label)
    context = tuple(context)
    check_ctx(context)
    return context, tuple(map(v, range(len(first)))), tuple(labels)


def piecewise(context, source, branches):
    equations = {}
    for inclusion, values in branches:
        for gen, term in zip(inclusion, values, strict=True):
            assert gen not in equations or equations[gen] == term
            equations[gen] = term
    return checked((equations[v(i)] for i in range(len(source))), source, context)


def compose(inner, outer):
    return tuple(subst_tm(t, outer) for t in inner)


def check_counits(seam, fixed, add_bead, counts):
    chart, src, tgt = glue(seam, seam, {i: v(i) for i in fixed})
    gens = tuple(map(v, range(len(seam))))
    retract = piecewise(seam, chart, [(src, gens), (tgt, gens)])
    if add_bead:
        # Extend a split chart by a genuine 1-generator with a nonvariable retraction.
        chart += (arr(STAR, src[0], tgt[0]),)
        retract = checked(retract + (identity(seam, v(0)),), chart, seam)
    layers, left, right = glue(chart, chart, {s[1]: t for s, t in zip(src, tgt)})
    all_gens = tuple(map(v, range(len(chart))))
    keep_left = piecewise(chart, layers, [(left, all_gens), (right, compose(retract, tgt))])
    keep_right = piecewise(chart, layers, [(left, compose(retract, src)), (right, all_gens)])
    # A preimage of a variable under a raw substitution has to be a variable.
    options = [[v(j) for j in range(len(layers)) if keep_left[j] == keep_right[j] == x]
               for x in all_gens]
    if add_bead:
        assert not options[-1]
        counts['split charts obstructed by an extra generator'] += 1
        return
    assert all(len(candidates) == 1 for candidates in options)
    diagonal = checked((xs[0] for xs in options), chart, layers)
    assert compose(diagonal, keep_left) == compose(diagonal, keep_right) == all_gens

    # Evaluate the two iterated diagonals in the same threefold amalgam.
    three, first_pair, third = glue(layers, chart,
                                    {s[1]: t for s, t in zip(src, compose(tgt, right))})
    first, second = compose(left, first_pair), compose(right, first_pair)
    last_pair = piecewise(three, layers, [(left, second), (right, third)])
    expand_left = piecewise(three, layers, [(left, compose(diagonal, first_pair)), (right, third)])
    expand_right = piecewise(three, layers, [(left, first), (right, compose(diagonal, last_pair))])
    assert compose(diagonal, expand_left) == compose(diagonal, expand_right)
    counts['unique coassociative chart diagonals'] += 1


def check_seams(counts):
    seam = (STAR, STAR, arr(STAR, v(0), v(1)), arr(STAR, v(1), v(0)))
    loop = comp2(seam, 0, v(2), v(3))
    seam += (arr(infer(seam, loop), loop, identity(seam, v(0))),)
    check_ctx(seam)
    for bits in product((False, True), repeat=len(seam)):
        fixed = {i for i, bit in enumerate(bits) if bit}
        if all(fv_ty(seam[i]) <= fixed for i in fixed):
            for extra in (False, True):
                check_counits(seam, fixed, extra, counts)


def planar(columns):
    # Collapse precisely the object intervals forced by empty 1-strings.
    poles = [0]
    for column in columns:
        poles.append(poles[-1] + (0 not in column))
    context = [STAR] * (poles[-1] + 1)

    def generator(ty):
        term = v(len(context))
        context.append(ty)
        return term

    rules, temporal = [], []
    for col, lengths in enumerate(columns):
        s, t = poles[col:col + 2]
        words, faces = [], []
        for length in lengths:
            vertices = [v(s)] + [generator(STAR) for _ in range(length - 1)] + [v(t)]
            edges = [generator(arr(STAR, vertices[j], vertices[j + 1])) for j in range(length)]
            path = edges[0] if edges else identity(tuple(context), v(s))
            for edge in edges[1:]:
                path = comp2(tuple(context), 0, path, edge)
            words.append(tuple(e[1] for e in edges))
            faces.append(path)
        beads = []
        for i, (a, b) in enumerate(zip(faces, faces[1:])):
            beads.append(generator(arr(infer(tuple(context), a), a, b)))
            rules.append((s, words[i], words[i + 1]))
        temporal.append(beads)
    ctx = tuple(context)
    check_ctx(ctx)
    return ctx, poles, rules, temporal


def bubble_search(ctx, poles, rules, bound):
    # Breadth-first search uses the actual occurrence, including its object at an empty cut.
    for origin in set(poles):
        seen = {()}
        current = {()}
        for _ in range(bound):
            following = set()
            for word in current:
                vertices = [origin] + [ctx[edge][3][1] for edge in word]
                for s, old, new in rules:
                    for i, vertex in enumerate(vertices):
                        if vertex != s or word[i:i + len(old)] != old:
                            continue
                        target = word[:i] + new + word[i + len(old):]
                        if not target:
                            return True
                        if target not in seen:
                            seen.add(target)
                            following.add(target)
            current = following
            if not current:
                break
    return False


def check_planar(counts):
    patterns = [xs for size in range(1, 5) for xs in product(range(3), repeat=size)]
    cases = [(p,) for p in patterns]
    cases.extend(product((p for p in patterns if len(p) == 2), repeat=2))
    for columns in cases:
        ctx, poles, rules, _ = planar(columns)
        predicted = any(c.count(0) >= 2 for c in columns)
        assert bubble_search(ctx, poles, rules, max(map(len, columns)) - 1) == predicted
        counts['planar charts with a bubble' if predicted else 'bubble-free planar charts'] += 1


def emit_sample(folder):
    ctx, poles, _, (beads,) = planar(((0, 2, 1, 0),))
    bubble = comp2(ctx, 1, comp2(ctx, 1, beads[0], beads[1]), beads[2])
    unit = identity(ctx, v(poles[0]))
    ty = arr(infer(ctx, unit), unit, unit)
    assert infer(ctx, bubble) == ty
    ordinary = Emitter()
    ordinary.check_type('three-bead-bubble', ctx, bubble, ty)
    (folder / 'OrdinaryUnitChart.agda').write_text(ordinary.module('OrdinaryUnitChart', ''))
    gray = Emitter()
    gray.check_type('suspended-bubble', susp_ctx(ctx), susp_tm(bubble), susp_ty(ty))
    module = gray.module('GrayUnitChart', '').replace('open import CaTTExp.Pure\n',
                                                     'open import CaTTExp.Gray.Pure\n')
    (folder / 'GrayUnitChart.agda').write_text(module)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    counts = Counter()
    check_seams(counts)
    check_planar(counts)
    if args.agda_dir:
        emit_sample(args.agda_dir)
    for label, count in counts.items():
        print(f'{count} {label}')
