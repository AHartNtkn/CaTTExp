"""Check transport of integral five-bracket weights through moving lower faces."""
from argparse import ArgumentParser
from collections import Counter
from pathlib import Path

from catt import STAR, arr, comp2, disc_tree, infer, subst_ty, tdim, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_branch_comparisons import cylinder
from gray_partial_cylinder_sections import selections
from gray_temporal_partial_actions import pad
from relative_coherence_based_columns import Brackets
from relative_coherence_cut import top_counts


def check_transport(old, marks, loop_power, output=None):
    t, u = range(len(old) - 2, len(old))
    full, minus, changes = cylinder(old, marks)
    plus = [v(x[1] + 1) if i in marks else x for i, x in enumerate(minus)]
    cap_slots = [row[slot][1] for row in (minus, plus) for slot in (t, u)]
    p = Brackets(7)
    values = []
    for i, ty in enumerate(full):
        actual = subst_ty(ty, values)
        if ty == STAR:
            value = v(0 if not values else 6)
        else:
            a, b = actual[2:]
            if tdim(ty) == 0:
                via = v(i % 5 + 1)
                first = p.bracket(a, via)
                second = p.bracket(via, b)
                for _ in range(loop_power):
                    loop = p.bracket(via, via)
                    first = comp2(p.ctx, 0, first, loop)
                value = comp2(p.ctx, 0, first, second)
            else:
                value = p.bracket(a, b)
                if i in cap_slots:
                    # Distinguish four cells even when their assigned faces coincide.
                    for _ in range(cap_slots.index(i)):
                        value = comp2(p.ctx, 3, ident(p.ctx, a), value)
        assert infer(p.ctx, value) == actual
        values.append(value)

    cov = {i: values[x[1]] for i, x in changes.items()}
    h, k = cov[t], cov[u]
    moves, framed = [], []
    for side, copy in enumerate((minus, plus)):
        x, y = (values[copy[slot][1]] for slot in (t, u))
        move = p.bracket(x, y)
        moves.append(move)
        frame = pad(p.ctx, old, v(t), cov, side)
        middle = frame(move)
        assert infer(p.ctx, middle) == arr(infer(p.ctx, frame(x)), frame(x), frame(y))
        assert top_counts(p.ctx, middle) == {move[1]: 1}
        framed.append(middle)

    before = comp2(p.ctx, 4, framed[0], k)
    after = comp2(p.ctx, 4, h, framed[1])
    assert infer(p.ctx, before) == infer(p.ctx, after)
    assert len({m[1] for m in (h, k, *moves)}) == 4
    expected = Counter([h[1], moves[1][1]])
    expected.subtract([moves[0][1], k[1]])
    for name, a, b, sign in [('forward', before, after, 1), ('back', after, before, -1)]:
        six = p.bracket(a, b)
        ty = arr(infer(p.ctx, a), a, b)
        assert infer(p.ctx, six) == ty
        counts = top_counts(p.ctx, b)
        counts.subtract(top_counts(p.ctx, a))
        assert counts == Counter({j: sign * n for j, n in expected.items()})
        if output:
            output.check_type(name, p.ctx, six, ty)


def main(path):
    disk = tree_ctx(disc_tree(4))
    ctx = disk + (disk[-1],)
    tops = {len(ctx) - 2, len(ctx) - 1}
    cases = [marks for marks in selections(ctx) if tops <= marks and
             all(tdim(ctx[i]) + 1 >= 2 for i in marks)]
    emitter = Emitter() if path else None
    biggest = max(cases, key=len)
    powers = [0, 1, 7]
    for marks in cases:
        for power in powers:
            output = emitter if marks == biggest and power == 0 else None
            check_transport(ctx, marks, power, output)
    print(f'{len(cases)} frame selections at powers {powers}; '
          'both signed six-boundaries and both five-slot counts in each.')
    if emitter:
        path.write_text(emitter.module(path.stem, 'Integral five-bracket transport in both directions.'))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    main(parser.parse_args().agda)
