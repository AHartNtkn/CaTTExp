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


def greatest(diagrams):
    diagrams = set(diagrams)
    assert diagrams
    for a, b in product(diagrams, repeat=2):
        assert tuple(map(join, a, b)) in diagrams
    return next(a for a in diagrams if all(tuple(map(join, a, b)) == a for b in diagrams))


def check_unitors(point, ctx, unit, b, emitter):
    disc = tree_ctx(disc_tree(1))
    f = v(len(disc) - 1)
    left = comp2(disc, 0, identity(disc, src(disc, f)), f)
    right = comp2(disc, 0, f, identity(disc, tgt(disc, f)))
    generic = [head(disc, a, z) for a, z in ((left, f), (f, left), (right, f), (f, right))]
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
