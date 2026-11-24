"""Check split pruning substitutions and their restrictions at other maximal cells."""
import argparse
from collections import Counter
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import STAR, arr, comp2, infer, maximal_vars, subst_tm, subst_ty, tgt, tree_ctx, v
from ct_suspension import ident
from partial_cylinder_steiner import trees
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_insertion_cut import Assertions
from semistrict_surface_unital_reassociation import check_rice, padded


def columns(tree):
    spans = {}
    index = 1

    def visit(children, parent):
        nonlocal index
        for i, child in enumerate(children):
            path = parent + (i,)
            arrow = index + 1
            index += 2
            visit(child, path)
            spans[path] = (arrow, index)

    visit(tree, ())
    return spans


def prune(tree, path):
    index, *rest = path
    if not rest:
        return tree[:index] + tree[index + 1:]
    return tree[:index] + (prune(tree[index], rest),) + tree[index + 1:]


def check_tree(tree, checks, counts):
    large = tree_ctx(tree)
    spans = columns(tree)
    peaks = {path: arrow for path, (arrow, stop) in spans.items() if stop == arrow + 1}
    assert set(peaks.values()) == set(maximal_vars(large))

    for path, peak in peaks.items():
        small = tree_ctx(prune(tree, path))
        source = large[peak][2][1]
        kept = [i for i in range(len(large)) if i not in (peak - 1, peak)]
        quotient = []
        for i, ty in enumerate(large):
            if i == peak:
                term = ident(small, quotient[source])
            elif i == peak - 1:
                term = quotient[source]
            else:
                term = v(kept.index(i))
            assert infer(small, term) == subst_ty(ty, quotient)
            quotient.append(term)
        counts['quotients'] += 1

        for keep_target in (False, True):
            neighbor = path[:-1] + (path[-1] + (-1 if keep_target else 1),)
            start, stop = spans.get(neighbor, (0, 0))
            section = []
            for ty, i in zip(small, kept, strict=True):
                term = v(i)
                if i == source and keep_target:
                    term = v(peak - 1)
                elif start <= i < stop:
                    args = (term, v(peak)) if keep_target else (v(peak), term)
                    term = comp2(large, len(path) - 1, *args)
                assert infer(large, term) == subst_ty(ty, section)
                section.append(term)
                composite = subst_tm(term, quotient)
                variable = v(len(section) - 1)
                assert padded(small, composite) == variable
                if composite != variable:
                    checks.equal(small, composite, variable, 'section entry')
            counts['sections'] += 1
            for other_path, other in peaks.items():
                if path == other_path or other_path[:len(neighbor)] == neighbor:
                    continue
                entry = section[kept.index(other)]
                assert entry == v(other)
                # Both substitutions are raw-typed, so all faces are preserved too.
                counts['protected peaks'] += 1


def mixed_attachment(binary):
    """Use a fresh 4-cell at a boundary changed by both pruning and reassociation."""
    base = tree_ctx(((), (), ()))
    f, g, h = map(v, maximal_vars(base))
    brackets = (comp2(base, 0, comp2(base, 0, f, g), h),
                comp2(base, 0, f, comp2(base, 0, g, h)))
    pole = ident(base, ident(base, v(0)))
    cell_type = arr(infer(base, pole), pole, pole)
    ctx = base + (cell_type, cell_type)
    z, zz = map(v, (len(base), len(base) + 1))
    left, right = [(comp2(ctx, 0, z, b), comp2(ctx, 0, zz, b)) for b in brackets]
    ctx += (arr(infer(ctx, right[0]), *right),)
    programs = {}
    for name, (a, b) in [('Mixed', left), ('Unit', right)]:
        padded_source = comp2(ctx, 2, a, ident(ctx, tgt(ctx, a)))
        assert infer(ctx, padded_source) == infer(ctx, b)
        syntax = Assertions()

        def show(ty):
            return '*' if ty == STAR else ' -> '.join(map(syntax.term, ty[2:]))

        variables = ' '.join(f'(x{i} : {show(ty)})' for i, ty in enumerate(ctx))
        result = show(arr(infer(ctx, b), padded_source, b))
        declaration = f'def fit {variables} : {result} = x{len(ctx) - 1}'
        programs[name] = '\n'.join([*syntax.commands, declaration, ''])
    with TemporaryDirectory() as folder:
        work = Path(folder)
        for name, program in programs.items():
            (work / f'{name}.catt').write_text(program)
        for name, mode, expect in [('Mixed', ['--sua'], True), ('Mixed', ['--su'], False),
                                   ('Unit', ['--su'], True), ('Unit', [], False)]:
            filename = name + '.catt'
            output = run(binary, work, filename, mode)
            if expect:
                accepted(output, filename, ['fit'])
            else:
                rejected(output, filename, 'fit')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--edges', type=int, default=5)
    parser.add_argument('--rice-binary', type=Path)
    options = parser.parse_args()
    checks, counts = Assertions(), Counter()
    for size in range(1, options.edges + 1):
        for tree in trees(size):
            check_tree(tree, checks, counts)
            counts['trees'] += 1
    print(dict(counts), dict(checks.count))
    if options.rice_binary:
        check_rice(checks, options.rice_binary, '--su')
        print('Rice verified every nonliteral section entry under strict units.')
        mixed_attachment(options.rice_binary.resolve())
        print('Rice checked the mixed attachment and its two controls.')
