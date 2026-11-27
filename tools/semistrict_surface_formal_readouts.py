"""Check compositions of two arbitrary readouts and successive formal substitutions."""
from argparse import ArgumentParser
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from catt import STAR, arr, comp2, disc_tree, infer, maximal_vars, src, sub_from, subst_tm, tgt, tree_ctx, v
from semistrict_surface_insertion_cut import Assertions, variables
from semistrict_surface_lower_charts import identity


def row(*dimensions):
    return tree_ctx(tuple(disc_tree(n - 1) for n in dimensions))


def top(ctx):
    return tuple(map(v, maximal_vars(ctx)))


def tuple_on(source, target, terms):
    return sub_from(source, target, dict(zip(maximal_vars(source), terms, strict=True)))


def history(ctx, a, b, swap):
    if swap:
        first = comp2(ctx, 0, src(ctx, a), b)
        last = comp2(ctx, 0, a, tgt(ctx, b))
    else:
        first = comp2(ctx, 0, a, src(ctx, b))
        last = comp2(ctx, 0, tgt(ctx, a), b)
    return comp2(ctx, 1, first, last)


def check(binary):
    p = row(3, 2)
    f, b = top(p)
    start = history(p, src(p, f), b, False)
    end = history(p, tgt(p, f), b, True)
    head = ('coh', p, arr(infer(p, start), start, end), variables(p))
    infer(p, head)

    def read(ctx, arrow, coeff):
        return subst_tm(head, tuple_on(p, ctx, (arrow, coeff)))

    q = row(3, 2, 2)
    f, b, c = top(q)
    first = tuple_on(p, q, (read(q, f, b), c))
    composite = subst_tm(head, first)
    positive = Assertions()
    negative = Assertions()
    for kill_f in (False, True):
        for kill_b in (False, True):
            for kill_c in (False, True):
                dims = [2 if kill_f else 3] + [2] * (2 - kill_b - kill_c)
                target = row(*dims)
                inputs = iter(top(target))
                a = next(inputs)
                f_image = identity(target, a, 2) if kill_f else a
                objects = [v(i) for i, ty in enumerate(target) if ty == STAR]

                def unit_at(index):
                    return identity(target, identity(target, objects[index], 0), 1)

                b_image = unit_at(1) if kill_b else next(inputs)
                c_image = unit_at(1 + int(not kill_b)) if kill_c else next(inputs)
                second = tuple_on(q, target, (f_image, b_image, c_image))
                direct_tuple = tuple(subst_tm(term, second) for term in first)
                result = subst_tm(composite, second)
                direct = subst_tm(head, direct_tuple)
                assert direct == result
                residual = f_image if kill_b else read(target, f_image, b_image)
                if not kill_c:
                    residual = read(target, residual, c_image)
                positive.equal(target, result, residual, 'nested readouts at their computed boundaries')
                if kill_f and not kill_b and kill_c:
                    source, target_pole = src(target, result), tgt(target, result)
                    assert infer(target, source) == infer(target, target_pole)
                    negative.equal(target, source, target_pole, 'opaque poles')
    positive.run(binary)
    with TemporaryDirectory() as directory:
        program = Path(directory) / 'opaque.catt'
        program.write_text('\n'.join(negative.commands) + '\n')
        proc = subprocess.run([binary, '--sua', program], capture_output=True, text=True)
        diagnostic = proc.stdout + proc.stderr
        assert 'Assertion failed: Terms' in diagnostic and 'are not equal' in diagnostic, diagnostic
    print('The surviving nullary readout has distinct poles under insertion.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('binary', type=Path)
    check(parser.parse_args().binary.resolve())
