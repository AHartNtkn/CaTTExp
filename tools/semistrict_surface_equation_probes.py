"""Construct variable-rule equality probes at a boundary with excessive Gray height."""
from argparse import ArgumentParser
from pathlib import Path

from catt import (arr, comp2, disc_tree, fv_tm, fv_ty, infer, maximal_vars, src, sub_from, subst_tm,
                  tdim_tm, tgt, tree_ctx, tree_of, v)
from ct_suspension import ident
from emit_agda import Emitter
from semistrict_surface_directed_power_queries import square


def append_bigon(ctx, faces):
    tree = tree_of(ctx)
    wide = tree_ctx(tree + (disc_tree(1),))
    assert wide[:len(ctx)] == ctx
    gate = v(len(wide) - 1)
    result = []
    for term in faces:
        end = term
        while tdim_tm(ctx, end) > 1:
            end = tgt(ctx, end)
        result.append(comp2(wide, 1, comp2(wide, 0, term, src(wide, gate)), comp2(wide, 0, end, gate)))
    return wide, result


def full_test(emitter, label, ctx, left, right, answer):
    boundary = infer(ctx, left)
    assert boundary == infer(ctx, right)
    emitter.checks.append(f'{label} : cohCase {emitter.ctx(ctx)} {emitter.ty(boundary)} '
                          f'{emitter.tm(left)} {emitter.tm(right)} ≡ {answer}\n{label} = refl\n')


def placed_rule(emitter):
    ctx = tree_ctx(disc_tree(2))
    z = v(len(ctx) - 1)
    loop_type = arr(infer(ctx, z), z, z)
    i = len(ctx)
    ctx += (loop_type,) * 3
    a, b, c = map(v, range(i, i + 3))
    before, after = comp2(ctx, 2, a, b), comp2(ctx, 2, b, c)
    rule = v(len(ctx))
    ctx += (arr(loop_type, before, after),)
    step = comp2(ctx, 2, comp2(ctx, 2, c, rule), a)
    left = comp2(ctx, 2, comp2(ctx, 2, c, before), a)
    right = comp2(ctx, 2, comp2(ctx, 2, c, after), a)
    target = arr(loop_type, left, right)
    assert infer(ctx, step) == target
    emitter.check_type('placedRule', ctx, step, target)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    ctx, exchange = square(3)
    u, v_term = src(ctx, exchange), tgt(ctx, exchange)
    same = comp2(ctx, 2, u, ident(ctx, tgt(ctx, u)))
    original = [u, same, v_term]
    middle, faces = append_bigon(ctx, original)
    wide, faces = append_bigon(middle, faces)
    collapse = {i: v(i) for i in maximal_vars(ctx)}
    endpoint = tgt(ctx, tgt(ctx, tgt(ctx, u)))
    for i in maximal_vars(wide):
        if i >= len(ctx):
            collapse[i] = ident(ctx, ident(ctx, endpoint))
    sigma = sub_from(wide, ctx, collapse)
    emitter = Emitter()
    placed_rule(emitter)
    for i, term in enumerate(faces):
        assert infer(wide, term) == infer(wide, faces[0])
        assert set(fv_tm(term)) | set(fv_ty(infer(wide, term))) == set(range(len(wide)))
        reduced = subst_tm(term, sigma)
        emitter.check_typed(f'clamped{i}', ctx, reduced)
        pairs = [(reduced, original[i])]
        for dim in range(tdim_tm(ctx, reduced), 0, -1):
            for j, (actual, expected) in enumerate(pairs):
                label = f'clamp{i}row{dim}side{j}'
                emitter.checks.append(f'{label} : ≈T (topS {emitter.tm(actual)}) '
                                      f'(topS {emitter.tm(expected)}) ≡ true\n{label} = refl\n')
            actual, expected = pairs[0]
            pairs = [(side(ctx, actual), side(ctx, expected)) for side in (src, tgt)]
        assert all(actual == expected for actual, expected in pairs)
        emitter.check_typed(f'padded{i}', wide, term)
    full_test(emitter, 'equalPair', wide, faces[0], faces[1], 'false')
    full_test(emitter, 'orderedPair', wide, faces[0], faces[2], 'false')
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = 'EquationProbes'
        code = emitter.module(module, __doc__)
        (args.agda_dir / (module + '.agda')).write_text(
            code.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))
    print('Constructed the equal and ordered probes at the same literal 3-boundary and checked coverage.')


if __name__ == '__main__':
    main()
