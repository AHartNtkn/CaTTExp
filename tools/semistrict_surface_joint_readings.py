"""Enumerate literal readings of scalar whiskerings and their shared seam."""
from argparse import ArgumentParser
from functools import cache
from itertools import product
from pathlib import Path

from catt import (STAR, TypeError_, arr, comp2, disc_tree, infer, mk_coh, src,
                  sub_from, subst_tm, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity


def finite_names(ctx, terms):
    """The globular set of names for all subterms, closed under signed faces."""
    indices, types = {}, []

    def visit(term):
        if term in indices:
            return v(indices[term])
        ty = infer(ctx, term)
        if ty != STAR:
            left, right = (visit(face) for face in ty[2:])
            named_type = arr(types[left[1]], left, right)
        else:
            named_type = STAR
        indices[term] = len(types)
        types.append(named_type)
        if term[0] == 'coh':
            for arg in term[3]:
                visit(arg)
        return v(indices[term])

    for term in terms:
        visit(term)
    return tuple(types), {term: v(i) for term, i in indices.items()}, tuple(indices)


def all_readings(names, atom):
    @cache
    def readings(term):
        results = [atom[term]]
        if term[0] == 'coh':
            for args in product(*(readings(arg) for arg in term[3])):
                reading = mk_coh(term[1], term[2], args)
                try:
                    infer(names, reading)
                except TypeError_:
                    continue
                results.append(reading)
        return tuple(results)
    return readings


def join(left, right):
    """Union of expanded head occurrences in two cuts of the same writing."""
    if left[0] == 'v':
        return right
    if right[0] == 'v':
        return left
    assert left[1:3] == right[1:3]
    return mk_coh(left[1], left[2], tuple(map(join, left[3], right[3])))


def meet(left, right):
    """Intersection of expanded occurrences in two cuts of one writing."""
    if left[0] == 'v':
        return left
    if right[0] == 'v':
        return right
    assert left[1:3] == right[1:3]
    return mk_coh(left[1], left[2], tuple(map(meet, left[3], right[3])))


def greatest(diagrams):
    diagrams = set(diagrams)
    assert diagrams
    for a, b in product(diagrams, repeat=2):
        assert tuple(map(join, a, b)) in diagrams
        assert tuple(map(meet, a, b)) in diagrams
    return next(a for a in diagrams if all(tuple(map(join, a, b)) == a for b in diagrams))


def check_separate_poles(point, context, unit, marker, generic, emitter):
    line = tree_ctx(((), ()))
    edges = [v(i) for i, ty in enumerate(line) if ty != STAR]
    l_form, _, r_form, _ = generic
    one = tree_ctx(disc_tree(1))

    def at(term, destination, argument):
        return subst_tm(term, sub_from(one, destination, {len(one) - 1: argument}))

    # The positions can be opened independently, even with the same old label.
    readings = [comp2(line, 0, src(line, at(form, line, edges[0])), edges[1])
                for form in (l_form, r_form)]
    names, atoms, _ = finite_names(point, (unit,))
    choices = atoms[unit], identity(names, atoms[v(0)])
    accepted = []
    for i, j in product(range(2), repeat=2):
        assignment = sub_from(line, names, {edges[0][1]: choices[i], edges[1][1]: choices[j]})
        left, right = [subst_tm(t, assignment) for t in readings]
        if left == right:
            accepted.append((i, j))
    assert accepted == [(1, 0), (1, 1)]

    # Construct the fitted comparison on the unfolded 2-disc, before folding
    # its top slot onto a marker at a compound identity face.
    two = tree_ctx(disc_tree(2))
    top = v(len(two) - 1)
    project = sub_from(two, context, {top[1]: marker})
    source, target = src(two, top), tgt(two, top)

    def frame(start, middle, end, ambient):
        return comp2(ambient, 1, start, comp2(ambient, 1, middle, end))

    for direction, l, li, r, ri in (('forward', *generic),
                                    ('backward', generic[2], generic[3], generic[0], generic[1])):
        p = frame(at(l, two, source), top, at(li, two, target), two)
        q = frame(at(r, two, source), top, at(ri, two, target), two)
        move_l = head(one, src(one, r), src(one, l))
        move_r = head(one, src(one, l), src(one, r))
        fitted = frame(at(move_l, two, source), p, at(move_r, two, target), two)
        compare = subst_tm(head(two, fitted, q), project)
        orig, dest = [subst_tm(t, project) for t in (p, q)]
        k, h = [at(t, point, unit) for t in (move_l, move_r)]
        pole = src(point, k)
        neutral = identity(point, pole)
        insert = head(two, top, frame(identity(two, source), top, identity(two, target), two))
        start = subst_tm(insert, sub_from(two, context, {top[1]: orig}))
        open_l = comp2(context, 1, head(point, neutral, k), comp2(context, 1, orig, neutral))
        open_r = comp2(context, 1, k, comp2(context, 1, orig, head(point, neutral, h)))
        result = comp2(context, 2, start, comp2(context, 2, open_l, comp2(context, 2, open_r, compare)))
        emitter.check_type(direction + 'SeparatePoles', context, result, arr(infer(context, orig), orig, dest))
    print('separate poles: least expansion (1, 0); two directed returns')


def check_unitors(point, ctx, unit, b, emitter):
    disc = tree_ctx(disc_tree(1))
    f = v(len(disc) - 1)
    left = comp2(disc, 0, identity(disc, src(disc, f)), f)
    right = comp2(disc, 0, f, identity(disc, tgt(disc, f)))
    generic = [head(disc, a, z) for a, z in ((left, f), (f, left), (right, f), (f, right))]
    check_separate_poles(point, ctx, unit, b, generic, emitter)
    at_unit = sub_from(disc, point, {f[1]: unit})
    l, li, r, ri = [subst_tm(t, at_unit) for t in generic]

    def collar(context, start, middle, end):
        return comp2(context, 1, start, comp2(context, 1, middle, end))

    u, w = collar(ctx, l, b, li), collar(ctx, r, b, ri)
    same, mixed = comp2(ctx, 1, u, u), comp2(ctx, 1, u, w)
    names, atom, evaluate = finite_names(ctx, (same, mixed))
    readings = all_readings(names, atom)
    at_name = sub_from(disc, names, {f[1]: atom[unit]})
    ln, lin, rn, rin = [subst_tm(t, at_name) for t in generic]
    move = subst_tm(head(disc, left, right), at_name)
    evaluated = subst_tm(move, evaluate)
    pole = comp2(point, 0, unit, unit)
    assert src(point, evaluated) == tgt(point, evaluated) == pole
    neutral = identity(point, pole)
    emitter.check_type('neutralizeReadingChange', point, head(point, evaluated, neutral),
                       arr(infer(point, evaluated), evaluated, neutral))
    first = collar(names, ln, atom[b], lin)
    second = collar(names, rn, atom[b], rin)
    assert greatest((t,) for t in readings(u)) == (first,)
    assert greatest((t,) for t in readings(w)) == (second,)
    mixed_first = collar(names, ln, atom[b], atom[li])
    mixed_second = collar(names, atom[r], atom[b], rin)
    for label, actual, pair in (('homogeneous', same, (first, first)),
                                ('mixed', mixed, (mixed_first, mixed_second))):
        reading = comp2(names, 1, *pair)
        candidates = readings(actual)
        assert greatest((t,) for t in candidates) == (reading,)
        assert subst_tm(reading, evaluate) == actual
        emitter.check_typed(label + 'CollarReading', names, reading)
        emitter.check_eq(label + 'CollarEvaluation', reading, evaluate, actual)
        print(f'{label}: {len(candidates)} literal readings of the collar composite')

    for label, start, end, inv_start, inv_end, source, target in (
            ('forward', l, r, li, ri, same, mixed),
            ('backward', r, l, ri, li, mixed, same)):
        step1 = comp2(ctx, 1, head(point, start, end), comp2(ctx, 1, b, inv_start))
        step2 = comp2(ctx, 1, end, comp2(ctx, 1, b, head(point, inv_start, inv_end)))
        repair = comp2(ctx, 1, u, comp2(ctx, 2, step1, step2))
        emitter.check_type(label + 'CollarRepair', ctx, repair, arr(infer(ctx, source), source, target))


def check(output):
    point = (STAR,)
    x = v(0)
    unit = identity(point, x)
    ctx = point + (arr(infer(point, unit), unit, unit),)
    b = v(1)
    left, right = comp2(ctx, 0, b, unit), comp2(ctx, 0, unit, b)
    names, atom, evaluate = finite_names(ctx, (comp2(ctx, 1, left, left), comp2(ctx, 1, left, right)))
    readings = all_readings(names, atom)
    free_unit = identity(names, atom[x])
    named_unit, named_b = atom[unit], atom[b]
    emitter = Emitter()
    examples = (
        ('same', left, left, comp2(names, 0, named_b, free_unit),
         comp2(names, 0, named_b, free_unit)),
        ('opposite', left, right, comp2(names, 0, named_b, named_unit),
         comp2(names, 0, named_unit, named_b)),
    )
    for label, first, second, expected_first, expected_second in examples:
        pairs = [(a, b2) for a, b2 in product(readings(first), readings(second))
                 if tgt(names, a) == src(names, b2)]
        a, b2 = greatest(pairs)
        assert (a, b2) == (expected_first, expected_second)
        reading = comp2(names, 1, a, b2)
        actual = comp2(ctx, 1, first, second)
        assert greatest((c,) for c in readings(actual)) == (reading,)
        assert subst_tm(reading, evaluate) == actual
        emitter.check_typed(label + 'Joint', names, reading)
        emitter.check_eq(label + 'Evaluation', reading, evaluate, actual)
        print(f'{label}: {len(pairs)} compatible joint readings')
    for term, expected in ((left, comp2(names, 0, named_b, free_unit)),
                           (right, comp2(names, 0, free_unit, named_b))):
        assert greatest((c,) for c in readings(term)) == (expected,)
    check_unitors(point, ctx, unit, b, emitter)
    if output is not None:
        output.mkdir(parents=True, exist_ok=True)
        module = 'JointBarReadings'
        program = emitter.module(module, __doc__).replace('CaTTExp.Pure', 'CaTTExp.Gray.Pure')
        (output / (module + '.agda')).write_text(program)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    check(parser.parse_args().agda_dir)
