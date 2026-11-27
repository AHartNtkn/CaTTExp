"""Check temporal substitutions inside a head on a suspended two-column tree."""
from argparse import ArgumentParser
from pathlib import Path

from catt import arr, chain_tree, comp2, infer, maximal_vars, src, sub_from, subst_tm, tgt, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_insertion_cut import variables


def chart(left, right):
    return tree_ctx(((chain_tree(left), chain_tree(right)),))


def bracket(ctx, slots, right):
    if len(slots) == 1:
        return slots[0]
    a, b, c = slots
    if right:
        return comp2(ctx, 2, a, comp2(ctx, 2, b, c))
    return comp2(ctx, 2, comp2(ctx, 2, a, b), c)


def assignment(source, target, entries):
    return sub_from(source, target, dict(zip(maximal_vars(source), entries, strict=True)))


def check_first_face(emitter):
    outer, line = tree_ctx(chain_tree(2)), tree_ctx(chain_tree(3))
    a, b = map(v, maximal_vars(outer))
    f, g, h = map(v, maximal_vars(line))
    composite = comp2(line, 0, f, g)
    substitution = assignment(outer, line, (composite, h))
    first_face = subst_tm(comp2(outer, 0, a, b), substitution)
    right = comp2(line, 0, f, comp2(line, 0, g, h))
    assert first_face == comp2(line, 0, composite, h)
    assert first_face != right
    emitter.check_type('firstFaceComparison', line, head(line, first_face, right),
                       arr(infer(line, right), first_face, right))
    emitter.checks.append(f'bracketingsDiffer : {emitter.tm(first_face)} ≡ {emitter.tm(right)} → ⊥\n'
                          'bracketingsDiffer ()\n')


def check_derived_seam(emitter):
    line = tree_ctx(chain_tree(3))
    f, g, h = map(v, maximal_vars(line))
    left = comp2(line, 0, comp2(line, 0, f, g), h)
    right = comp2(line, 0, f, comp2(line, 0, g, h))
    boundary = infer(line, left)
    ctx = line + (arr(boundary, left, left), arr(boundary, right, right))
    a, b = v(len(line)), v(len(line) + 1)
    assert tgt(ctx, a) != src(ctx, b)
    bridge = head(line, left, right)
    result = comp2(ctx, 1, a, comp2(ctx, 1, bridge, b))
    emitter.check_type('composeAcrossDerivedSeam', ctx, result, arr(boundary, left, right))


def check_moving_boundary(emitter):
    wing = tree_ctx((chain_tree(1), (), ()))
    alpha, g, h = map(v, maximal_vars(wing))
    before = comp2(wing, 0, comp2(wing, 0, alpha, g), h)
    after = comp2(wing, 0, alpha, comp2(wing, 0, g, h))
    line = tree_ctx(chain_tree(3))
    x, y, z = map(v, maximal_vars(line))
    left = comp2(line, 0, comp2(line, 0, x, y), z)
    right = comp2(line, 0, x, comp2(line, 0, y, z))
    enter = subst_tm(head(line, right, left), assignment(line, wing, (src(wing, alpha), g, h)))
    leave = subst_tm(head(line, left, right), assignment(line, wing, (tgt(wing, alpha), g, h)))
    fitted = comp2(wing, 1, enter, comp2(wing, 1, before, leave))
    assert infer(wing, before) != infer(wing, after)
    assert infer(wing, fitted) == infer(wing, after) and fitted != after
    to_fitted, from_fitted = head(wing, after, fitted), head(wing, fitted, after)

    beta = v(len(wing))
    ctx = wing + (infer(wing, alpha),)
    second = assignment(wing, ctx, (beta, g, h))
    witness = v(len(ctx))
    ctx += (arr(infer(ctx, before), before, subst_tm(before, second)),)
    moved = comp2(ctx, 1, enter, comp2(ctx, 1, witness, leave))
    result = comp2(ctx, 2, to_fitted, comp2(ctx, 2, moved, subst_tm(from_fitted, second)))
    emitter.check_type('returnAtMovingSphere', ctx, result,
                       arr(infer(ctx, after), after, subst_tm(after, second)))


def check(emitter):
    p = chart(1, 1)
    f, g = map(v, maximal_vars(p))
    serial = comp2(p, 2, comp2(p, 1, f, src(p, g)), comp2(p, 1, tgt(p, f), g))
    operation = ('coh', p, infer(p, serial), variables(p))

    def reading(ctx, left_size, left_right, right_right):
        labels = list(map(v, maximal_vars(ctx)))
        entries = (bracket(ctx, labels[:left_size], left_right),
                   bracket(ctx, labels[left_size:], right_right))
        return subst_tm(operation, assignment(p, ctx, entries))

    q = chart(3, 3)
    slots = list(map(v, maximal_vars(q)))
    fs, gs = slots[:3], slots[3:]
    paths = []
    for left_first in (True, False):
        steps = []
        for step, move_left in enumerate((left_first, not left_first)):
            n, m = (3, 1) if move_left else (1, 3)
            local = chart(n, m)
            comparison = head(local, reading(local, n, False, False),
                              reading(local, n, move_left, not move_left))
            entries = (fs if move_left else [bracket(q, fs, step == 1)])
            entries = entries + ([bracket(q, gs, step == 1)] if move_left else gs)
            steps.append(subst_tm(comparison, assignment(local, q, entries)))
        paths.append(comp2(q, 3, *steps))
    assert paths[0] != paths[1]
    forward, reverse = head(q, *paths), head(q, *reversed(paths))
    loop = comp2(q, 4, forward, reverse)
    cap = head(q, loop, identity(q, paths[0]))

    # The six 3-positions specialize to two loops on nonvariable 2-faces.
    target = tree_ctx((chain_tree(4),))
    a, b, c, d = map(v, maximal_vars(target))
    for first, second in ((a, b), (c, d)):
        pole = comp2(target, 1, first, second)
        target += (arr(infer(target, pole), pole, pole),)
    alpha, beta = v(len(target) - 2), v(len(target) - 1)
    fold = assignment(q, target, [alpha] * 3 + [beta] * 3)
    left, right, move, back, filled = (subst_tm(term, fold)
                                      for term in (*paths, forward, reverse, cap))
    assert left != right and infer(target, left) == infer(target, right)
    emitter.check_type('betweenSchedules', target, move, arr(infer(target, left), left, right))
    emitter.check_type('returnSchedule', target, back, arr(infer(target, left), right, left))
    round_trip = comp2(target, 4, move, back)
    emitter.check_type('fillReturn', target, filled,
                       arr(infer(target, round_trip), round_trip, identity(target, left)))

    # Attach once at a computed schedule and transport at the opposite one.
    # A fresh parallel cell avoids assuming the track is a loop.
    start = v(len(target))
    target += (infer(target, left),)
    witness = v(len(target))
    target += (arr(infer(target, left), start, left),)
    emitter.check_type('atCompoundAttachment', target, comp2(target, 4, witness, move),
                       arr(infer(target, right), start, right))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    out = parser.parse_args().directory
    emitter = Emitter()
    check(emitter)
    check_first_face(emitter)
    check_derived_seam(emitter)
    check_moving_boundary(emitter)
    out.mkdir(parents=True, exist_ok=True)
    module = 'DirectedTemporalFaces'
    program = emitter.module(module, __doc__).replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure')
    (out / (module + '.agda')).write_text(program)
    print('Generated seven Gray judgments and the literal first-face inequality.')
