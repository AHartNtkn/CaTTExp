"""Assemble the three-by-four globe tensor from its two remaining short lifts."""
import argparse
from collections import Counter
from pathlib import Path

from canonical_gray_two_discs import tableau_interpreter
from catt import STAR, arr, check_ctx, comp2, infer, src, tgt, v
from emit_agda import Emitter
from gray_globe_attachments import ordered_factors
from gray_globe_comparison import atom, face
from gray_globe_corner_prisms import fold
from gray_globe_exterior_actions import arity
from gray_globe_factorizations import profile, truncate
from gray_globe_natural_exchanges import top_sites, word
from gray_globe_section import EMPTY_ROW, cells
from gray_globe_strip_squares import lift_on
from gray_path_wedge import compose


def assemble(emitter=None):
    domain = cells((3, 4)) - {()}
    terms, values, exchanges = {}, [], {}
    ctx = ()
    sixes = Counter()
    pending = set()

    def parameter(value, ty):
        nonlocal ctx
        result = v(len(ctx))
        ctx += (ty,)
        values.append(value)
        return result

    def write(steps):
        args = [section(c) for c in steps]
        return fold(ctx, 4, args)

    def rebracket(steps, a, b):
        if a == b:
            return []
        args = [section(c) for c in steps]
        return [lift_on(ctx, arity(4, (5,)*len(args)), args, a, b)]

    def change(old_steps, new_steps, old, new):
        """Cross a fork, if present, using the exchange at its actual four corners."""
        if old_steps == new_steps:
            return rebracket(old_steps, old, new)
        i, j = [k for k, (a, b) in enumerate(zip(old_steps, new_steps, strict=True)) if a != b]
        assert j == i+1 and len(old_steps) == 3
        patch = compose(*old_steps[i:j+1], 4)
        assert top_sites(patch) == ((1, 4), (3, 2)) and compose(*new_steps[i:j+1], 4) == patch
        a, b = write(old_steps[i:j+1]), write(new_steps[i:j+1])
        key = (patch, a, b)
        if key not in exchanges:
            exchanges[key] = parameter(patch+(EMPTY_ROW,), arr(infer(ctx, a), a, b))
        move = exchanges[key]
        fixed = section(old_steps[2 if i == 0 else 0])
        step = comp2(ctx, 4, move, fixed) if i == 0 else comp2(ctx, 4, fixed, move)
        return rebracket(old_steps, old, src(ctx, step)) + [step] + rebracket(new_steps, tgt(ctx, step), new)

    def long(w, p):
        predecessors = {(p[0]-1, p[1]), (p[0], p[1]-1)}
        owner = {q: -1 if q in predecessors or q == p else q[0] for q in profile(w) if sum(q) > 4}
        parts = ordered_factors(w, 4, owner)
        assert sorted(map(len, parts)) == [6, 7]
        core = next(c for c in parts if len(c) == 7)
        assert set(top_sites(face(core, 0))) == predecessors
        args = [section(c) for c in parts]
        middle = comp2(ctx, 4, *args)
        changes = []
        for side, op in enumerate((src, tgt)):
            z = face(w, side)
            chosen_steps = tuple(word(z))
            raw_steps = tuple(u for c in parts for u in word(truncate(c, 5, side)))
            chosen, raw = section(z), op(ctx, middle)
            changes.append(change(raw_steps, chosen_steps, raw, chosen) if side else
                           change(chosen_steps, raw_steps, chosen, raw))
        return fold(ctx, 5, changes[0] + [middle] + changes[1])

    def section(c):
        if c in terms:
            return terms[c]
        d = len(c)-1
        if d:
            s, t = (section(face(c, i)) for i in (0, 1))
            ty = arr(infer(ctx, s), s, t)
        else:
            ty = STAR
        native = d >= 4 and (3, 1) not in top_sites(truncate(c, 4, 0))
        if d == 6 and native:
            assert (3, 3) not in profile(c)
            sixes['width two'] += 1
        if d <= 4 or native or d == 7:
            term = parameter(c, ty)
        elif d == 5:
            term = parameter(c, ty) if len(top_sites(c)) == 1 else write(word(c))
        elif len(top_sites(c)) > 1:
            args = [section(u) for u in word(c)]
            term = fold(ctx, 5, args)
            sixes['two six-steps'] += 1
        else:
            p, = top_sites(c)
            if len(c[5][0]) == 2:
                if p == (2, 4):
                    assert profile(c) - profile(atom(c[-1][0][0])) == {(3, 0), (3, 1)}
                    pending.add(c)
                    sixes['short rival'] += 1
                else:
                    assert p == (3, 3)
                    sixes['short central'] += 1
                term = parameter(c, ty)
            else:
                term = long(c, p)
                sixes['three-event faces'] += 1
        assert infer(ctx, term) == ty
        terms[c] = term
        return term

    top, = (c for c in domain if len(c) == 8)
    section(top)
    if emitter:
        emitter.check_typed('three-by-four-context-top', ctx, terms[top])
        for side in (0, 1):
            f = face(top, side)
            s, t = (terms[face(f, i)] for i in (0, 1))
            emitter.check_type('three-by-four-facet-' + str(side), ctx, terms[f], arr(infer(ctx, s), s, t))
    for c in sorted(domain, key=lambda x: (len(x), x)):
        section(c)
    check_ctx(ctx)
    evaluate = tableau_interpreter(ctx, values.__getitem__)
    assert all(evaluate(t) == c for c, t in terms.items())
    assert all(terms[atom(g)][0] == 'v' for c in domain for g in c[-1][0])
    assert len(pending) == 2
    assert {c[-1][0][0][0][1] for c in pending} == {0, 1}
    assert len({p for p, _, _ in exchanges}) == len(exchanges) == 2
    assert sixes == {'width two': 4, 'short central': 4, 'short rival': 2,
                     'three-event faces': 4, 'two six-steps': 2}
    print('Intrinsic cells by degree:', sorted(Counter(len(c)-1 for c in terms).items()))
    print('Six-cell constructions:', dict(sorted(sixes.items())))
    print('Two signed exchanges used. Remaining hypotheses: two short (2,4) lifts with (3,1) padding.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    assemble(emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Three-by-four assembly with two short-lift hypotheses.'))
