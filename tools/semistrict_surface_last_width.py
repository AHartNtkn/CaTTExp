"""Check last-boundary width fitting, including substitution in a raised operation."""
import argparse
from itertools import islice
from pathlib import Path
import re
from tempfile import TemporaryDirectory

from catt import (STAR, arr, comp2, glue_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, tdim, tgt, tree_ctx, v)
from relative_coherence_exchange_faces import head
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_insertion_cut import Assertions
from semistrict_surface_scalar_pairs import splice
from semistrict_surface_width_thresholds import template_cases


def check_converted_input(binary, folder, code, params, boundary, fit):
    # Specialize the rank-two example at a 2-input that needs width one.
    # Give the three new high generators raw declarations using its fitted form.
    inner = glue_tree(1, 0, 1)
    generic, tower = islice(template_cases(inner), 2)
    joined = tree_ctx(splice(inner, (0,), inner))
    sigma = tuple(v(tdim(ty) + 1) for ty in joined)
    left, right = map(code.term, (tower.left, tower.right))

    def bridge(start, end):
        return code.term(subst_tm(head(joined, start, end), sigma))

    fwd = bridge(generic.left, generic.right)
    back = bridge(generic.right, generic.left)
    base = f'{tower.context} (y : {left} -> {left}) (z : {right} -> {right})'
    repaired = f'comp[y,comp[{fwd},z,{back}]]'

    def specialize(expression, top):
        return re.sub(r'\bx[12]\b', lambda m: {'x1': left, 'x2': top}[m[0]], expression)

    higher = params[params.index('(x3 :'):]
    context = f'{base} {specialize(higher, repaired)}'
    old = specialize(boundary, repaired)
    fitted = specialize(fit, 'comp[y,z]')
    (folder/'Heads.catt').write_text('\n'.join(code.commands)+'\n')
    (folder/'Mixed.catt').write_text(
        f'import Heads\ndef mixed {context} : {old} -> {old} = comp[{fitted},r]\n')
    (folder/'MixedClass.catt').write_text(
        f'import Heads\ndef mixed_class {context} : comp[{fitted},r] -> comp[p,r] = id(comp[p,r])\n')
    (folder/'Base.catt').write_text(
        f'import Heads\ndef old_query {context} : {old} -> {old} = r\n'
        f'def seam {base} : {left} -> {left} = z\n')
    weak = run(binary, folder, 'Base.catt')
    if 'Checking old_query\n' not in weak:
        raise ValueError(weak)
    rejected(weak, 'Base.catt', 'seam')
    accepted(run(binary, folder, 'Base.catt', ['--insertion-width', '1']),
             'Base.catt', ['old_query', 'seam'])
    accepted(run(binary, folder, 'Mixed.catt', ['--insertion-width', '1']), 'Mixed.catt', ['mixed'])
    accepted(run(binary, folder, 'MixedClass.catt', ['--sua']), 'MixedClass.catt', ['mixed_class'])
    print('Width-one converted input in a width-two comparison over raw attachments')


def check(binary, folder, rank):
    inner = glue_tree(rank, 0, rank)
    generic, tower = islice(template_cases(inner), 2)
    context = tree_ctx(splice(inner, (0,), inner))
    labels = tuple(v(tdim(ty) + 1) for ty in context)
    loops = (STAR,)
    for i in range(rank):
        loops += (arr(loops[-1], v(i), v(i)),)
    code = Assertions()
    last = tgt(loops, tower.left)
    stationary = v(len(loops))
    extended = (*loops, arr(infer(loops, last), last, last))
    last_text = code.term(last)
    declaration = f'{tower.context} (x{len(loops)} : {last_text} -> {last_text})'

    # Independently build the operation on the raised arity. Specialization
    # inserts the comparison in its first slot and a free variable in the second.
    raised = tree_ctx(glue_tree(rank+1, rank-1, rank))
    varying, fixed = maximal_vars(raised)
    before = comp2(raised, rank-1, src(raised, v(varying)), v(fixed))
    after = comp2(raised, rank-1, tgt(raised, v(varying)), v(fixed))
    operation = head(raised, before, after)

    def carry(start, end):
        comparison = subst_tm(head(context, start, end), labels)
        substitution = sub_from(raised, extended, {varying: comparison, fixed: stationary})
        return subst_tm(operation, substitution)

    enter = carry(generic.right, generic.left)
    leave = carry(generic.left, generic.right)
    a = code.term(src(extended, enter))
    b = code.term(tgt(extended, enter))
    assert infer(extended, leave)[2:] == infer(extended, enter)[2:][::-1]
    enter_text, leave_text = code.term(enter), code.term(leave)
    params = f'{declaration} (p : {b} -> {b}) (r : {a} -> {a})'
    fit = f'comp[{enter_text},p,{leave_text}]'
    (folder/'Heads.catt').write_text('\n'.join(code.commands)+'\n')
    (folder/'Fit.catt').write_text(
        f'import Heads\ndef fit {params} : {a} -> {a} = {fit}\n'
        f'def fit_argument {params} : {a} -> {a} = comp[{fit},r]\n')
    (folder/'Direct.catt').write_text(
        f'import Heads\ndef direct {params} : {a} -> {a} = comp[p,r]\n')
    # Keep p and r distinct, so a fit of the boundary alone cannot pass this test.
    (folder/'Class.catt').write_text(
        f'import Heads\ndef same {params} : comp[{fit},r] -> comp[p,r] = id(comp[p,r])\n')
    (folder/'Order.catt').write_text(
        f'import Heads\ndef opposite {params} : comp[{fit},r] -> comp[r,p] = id(comp[r,p])\n')
    for mode in ([], ['--insertion-width', str(rank-1)]):
        accepted(run(binary, folder, 'Fit.catt', mode), 'Fit.catt', ['fit', 'fit_argument'])
    # Check a variable at the changed boundary separately: its failure has a
    # specific inferred-type diagnostic, independent of argument elaboration.
    (folder/'Var.catt').write_text(f'import Heads\ndef direct_var {params} : {a} -> {a} = p\n')
    rejected(run(binary, folder, 'Var.catt', ['--insertion-width', str(rank-1)]),
             'Var.catt', 'direct_var')
    for mode in (['--insertion-width', str(rank)], ['--sua']):
        accepted(run(binary, folder, 'Direct.catt', mode), 'Direct.catt', ['direct'])
        accepted(run(binary, folder, 'Class.catt', mode), 'Class.catt', ['same'])
        rejected(run(binary, folder, 'Order.catt', mode), 'Order.catt', 'opposite')
    print(f'Rank {rank}: checked raised comparisons, fitted inputs and specified class')
    if rank == 2:
        check_converted_input(binary, folder, code, params, a, fit)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('binary', type=Path)
    parser.add_argument('--ranks', type=int, default=6)
    args = parser.parse_args()
    with TemporaryDirectory() as tmp:
        for rank in range(1, args.ranks+1):
            check(args.binary.resolve(), Path(tmp), rank)
