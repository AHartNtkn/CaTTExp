"""Compare both top cuts with the actual choices of the (2,2) attachment."""
import argparse
from collections import Counter
from functools import cache
from pathlib import Path

from canonical_gray_two_discs import tableau_interpreter
from catt import comp2, infer, maximal_vars, sub_from, subst_tm, v
from emit_agda import Emitter
from gray_globe_attachments import blocks
from gray_globe_comparison import atom, face, strict_cells
from gray_globe_exterior_actions import arity, certificate, coherence, comparison
from gray_globe_factorizations import profile, truncate
from gray_globe_section import cells
from gray_globe_sector_terms import arrow, verify
from gray_globe_strip_gluing import chart_or_hole, factors
from gray_path_wedge import compose


CENTER = (2, 2)
CRITICAL_ROW = {(1, 3), CENTER, (3, 1)}


def endpoints():
    return {z for cell in strict_cells((5, 5), 5)
            if cell[-1][0] and chart_or_hole(cell, 2, 2) == (3, 2)
            for z in (truncate(cell, 4, s) for s in (0, 1))
            if chart_or_hole(z, 2, 2) == (2, 3)}


def check_strip_faces():
    """Check which section supplies each face in the direct gluing criterion."""
    @cache
    def choice(c):
        sites = profile(c)
        if len(c) < 5:
            return 'common'
        if not {(1, 3), CENTER} <= sites:
            return 'A'
        if (3, 1) not in sites:
            return 'B'
        if (2, 3) not in sites:
            return 'A'
        return 'corrected B' if (3, 2) not in sites else 'split'

    counts = Counter()
    for c in cells((5, 5)):
        if len(c) < 5 or (3, 3) in profile(c):
            continue
        branch = choice(c)
        counts[branch] += 1
        if branch == 'split':
            parts = factors(c, (3, 3))
            assert {choice(p) for p in parts} == {'A', 'corrected B'}
        elif branch == 'A':
            assert (2, 3) not in profile(c)
        else:
            assert (3, 2) not in profile(c)
        for side in (0, 1):
            z = face(c, side)
            if len(z) < 5:
                assert choice(z) == 'common'
            elif len(z) == 5 and branch in ('split', 'corrected B'):
                assert choice(z) == 'A' and CRITICAL_ROW <= profile(z)
            else:
                assert choice(z) == branch
                if branch == 'split':
                    assert factors(z, (3, 3)) == tuple(truncate(p, len(z)-1, side) for p in parts)
    print('Intrinsic cells of height at least four by gluing rule:', dict(sorted(counts.items())))


def prescribed(z, hole):
    """Expand the two prescribed operands by the actual attachment rule."""
    halves = factors(z, hole)
    groups = [blocks(part, CENTER) if CENTER in profile(part) else (part,)
              for part in halves]
    assert sorted(map(len, groups)) == [1, 2]
    word = groups[0] + groups[1]
    return word, len(groups[0]) == 2


def bracket(ctx, items, left):
    a, b, c = items
    if left:
        return comp2(ctx, 3, comp2(ctx, 3, a, b), c)
    return comp2(ctx, 3, a, comp2(ctx, 3, b, c))


def instantiate(head, ctx, items):
    ar = head[1]
    sigma = sub_from(ar, ctx, dict(zip(maximal_vars(ar), items, strict=True)))
    return subst_tm(head, sigma)


@cache
def associator(left):
    ctx = arity(3, (4, 4, 4))
    slots = list(map(v, maximal_vars(ctx)))
    return coherence(ctx, bracket(ctx, slots, left), bracket(ctx, slots, not left))


def witness(ctx, chosen, source, target):
    old, old_left = source
    new, new_left = target
    a = [chosen[p] for p in old]
    b = [chosen[p] for p in new]
    if old == new:
        assert old_left != new_left
        return instantiate(associator(old_left), ctx, a), 'chain'

    center, = (i for i, p in enumerate(old) if CENTER in profile(p))
    assert center in (0, 2) and old[center] == new[center]
    pair_first = center == 2
    j = 0 if pair_first else 1
    patch = compose(old[j], old[j+1], 3)
    assert patch == compose(new[j], new[j+1], 3)
    spatial = [chosen[p] for p in factors(patch, CENTER)]
    pair_type = arrow(ctx, comp2(ctx, 3, *a[j:j+2]), comp2(ctx, 3, *b[j:j+2]))
    exchange, = (t for head in comparison(2, (4, 4))
                 if infer(ctx, t := instantiate(head, ctx, spatial)) == pair_type)
    steps = []
    if old_left != pair_first:
        steps.append(instantiate(associator(old_left), ctx, a))
    steps.append(comp2(ctx, 3, exchange, a[center]) if pair_first
                 else comp2(ctx, 3, a[center], exchange))
    if new_left != pair_first:
        steps.append(instantiate(associator(pair_first), ctx, b))
    result = steps[0]
    for step in steps[1:]:
        result = comp2(ctx, 4, result, step)
    return result, 'center-last' if pair_first else 'center-first'


def check(emitter):
    check_strip_faces()
    critical = {z for z in strict_cells((5, 5), 4)
                if CRITICAL_ROW <= profile(z)}
    assert critical == endpoints()
    cases = [(z, prescribed(z, (2, 3)), prescribed(z, (3, 2))) for z in sorted(critical)]
    exterior, centers = set(), set()
    for _, (word, _), (other, _) in cases:
        for p in word + other:
            if CENTER in profile(p):
                centers.add(p)
                exterior.update(face(p, side) for side in (0, 1))
            else:
                exterior.add(p)
        if word != other:
            pair = [p for p in word if CENTER not in profile(p)]
            exterior.update(factors(compose(*pair, 3), CENTER))

    ctx, names, chosen = verify(5, 5, None, required=exterior)
    values = list(map(atom, names))
    # Universally quantified central lifts with the prescribed literal faces.
    for p in sorted(centers):
        assert len(p[-1][0]) == 1
        ends = [chosen[face(p, side)] for side in (0, 1)]
        chosen[p] = v(len(ctx))
        ctx += (arrow(ctx, *ends),)
        values.append(p)
    evaluate = tableau_interpreter(ctx, values.__getitem__)
    for p in centers:
        ty = infer(ctx, chosen[p])
        assert tuple(map(evaluate, ty[2:])) == (face(p, 0), face(p, 1))
    certify = certificate(emitter, ctx) if emitter else None
    counts = Counter()
    for z, first, second in cases:
        for source, target in ((first, second), (second, first)):
            proof, kind = witness(ctx, chosen, source, target)
            ends = [bracket(ctx, [chosen[p] for p in word], left) for word, left in (source, target)]
            wanted = arrow(ctx, *ends)
            assert infer(ctx, proof) == wanted
            assert all(evaluate(t) == z for t in ends)
            assert evaluate(proof) == z + (((), ()),)
            key = kind, source == first
            if certify and not counts[key]:
                certify(f'{kind}-{"forward" if source == first else "reverse"}', proof, wanted)
            counts[key] += 1
    assert sum(counts.values()) == 288
    print(f'{len(cases)} labelled endpoints, {len(centers)} central parameters')
    print('Witnesses by order and direction:', dict(sorted(counts.items())))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    check(emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Comparisons for three attachment blocks.'))
