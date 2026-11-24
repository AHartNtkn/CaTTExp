"""Test the least insertion width on generic trees, folded loops and scalar masks."""
import argparse
from collections import Counter
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory

from catt import STAR, arr, glue_tree, infer, subst_tm, subst_ty, tdim, tree_ctx, v
from ct_suspension import ident
from partial_cylinder_steiner import trees
from relative_coherence_exchange_faces import head
from semistrict_surface_elementary_insertions import exterior
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_insertion_cut import Assertions, shape, standard, variables
from semistrict_surface_moore_insertion import height
from semistrict_surface_scalar_pairs import branches, positions, splice, trunk


@dataclass
class Query:
    family: str
    context: str
    left: tuple
    right: tuple
    width: int


def common_prefix_length(paths):
    return next((i for i, column in enumerate(zip(*paths)) if len(set(column)) > 1),
                len(paths[0]))


def template_cases(inner):
    d, j = height(inner), trunk(inner)
    outer = glue_tree(d, j, d)
    joined, exterior_map = exterior(outer, (0,)*(j+1), inner)
    ctx = tree_ctx(joined)
    top = standard(tree_ctx(outer), d)
    left = subst_tm(top, exterior_map)
    right = ('coh', ctx, subst_ty(top[2], exterior_map), variables(ctx))
    assert infer(ctx, left) == infer(ctx, right)
    yield Query('generic', shape(ctx), left, right, d-j)

    tower = [STAR]
    written = '(x0 : *)'
    for r in range(1, d+1):
        tower.append(arr(tower[-1], v(r-1), v(r-1)))
        written += f' (x{r} : x{r-1} -> x{r-1})'
    sigma = tuple(v(tdim(ty)+1) for ty in ctx)
    yield Query('tower', written, subst_tm(left, sigma), subst_tm(right, sigma), d-j)

    units = [v(0)]
    for _ in range(d):
        units.append(ident((STAR,), units[-1]))
    scalar = (STAR, infer((STAR,), units[d]))
    port = 'x0'
    for _ in range(d-1):
        port = f'id({port})'
    written = f'(x0 : *) (x1 : {port} -> {port})'
    peaks = positions(inner, d)
    joined_peaks = positions(joined, d)
    assert joined_peaks[:-1] == peaks
    for size in range(len(peaks)+1):
        for selected in combinations(peaks, size):
            top_labels = iter(v(1) if p in selected or p == joined_peaks[-1] else units[d]
                              for p in joined_peaks)
            sigma = tuple(next(top_labels) if tdim(ty)+1 == d else units[tdim(ty)+1]
                          for ty in ctx)
            a, b = subst_tm(left, sigma), subst_tm(right, sigma)
            assert infer(scalar, a) == infer(scalar, b)
            width = d-common_prefix_length(selected) if selected else 0
            yield Query('scalar mask', written, a, b, width)


def check_queries(binary, limit):
    shapes = [tree for size in range(1, limit+1) for tree in trees(size)]
    queries = [q for t in shapes if height(t) > trunk(t) for q in template_cases(t)]
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        code = Assertions()
        cases = []
        for i, q in enumerate(queries):
            left, right = code.term(q.left), code.term(q.right)
            path = folder/f'case{i}.catt'
            path.write_text(f'assert {left} = {right} in {q.context}\n')
            cases.append(path.name)
        (folder/'heads.catt').write_text('\n'.join(code.commands)+'\n')
        high = max(q.width for q in queries)
        modes = [(['--insertion-width', str(b)], b) for b in range(high+1)]
        for flags, b in modes+[(['--su'], 0), (['--sua'], high)]:
            result = subprocess.run([binary, *flags, 'heads.catt', *cases], cwd=folder,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    check=True)
            log = re.sub(r'\x1b\[[0-9;]*m', '', result.stdout)
            sections = re.split(r'^Importing case(\d+)\.catt$', log, flags=re.M)
            assert 'Finished importing heads.catt' in sections[0] and 'Error:' not in sections[0]
            assert list(map(int, sections[1::2])) == list(range(len(queries)))
            hits = 0
            for q, section in zip(queries, sections[2::2], strict=True):
                if b >= q.width:
                    if 'are equal' not in section or 'Error:' in section:
                        raise AssertionError((flags, q.family, q.width, section))
                    hits += 1
                elif 'Error: Assertion failed:' not in section or 'are not equal' not in section:
                    raise AssertionError((flags, q.family, q.width, section))
            print(f'{" ".join(flags)}: {hits} equal, {len(queries)-hits} unequal')
    print(dict(Counter(q.family for q in queries)))


def check_residuals(limit):
    shapes = [t for size in range(limit+1) for t in trees(size)]
    counts = Counter()
    for t in shapes:
        for path, d in branches(t):
            for u in shapes:
                if height(u) > d or trunk(u) < len(path)-1:
                    continue
                residual = splice(t, path, u)
                if height(t) == trunk(t):
                    assert residual == u
                else:
                    assert height(residual) <= height(t) and trunk(residual) >= trunk(t)
                counts['nested residuals'] += 1
    print(dict(counts))


def check_nested(binary):
    shapes = [t for size in range(5) for t in trees(size)]
    programs = {}
    for t in shapes:
        d, j = height(t), trunk(t)
        if d == j:
            continue
        outer = glue_tree(d, j, d)
        first = (0,)*(j+1)
        middle, outside = exterior(outer, first, t)
        original = standard(tree_ctx(outer), d)
        after_first = subst_ty(original[2], outside)
        for q, leaf in branches(t):
            for u in shapes:
                if height(u) > leaf or trunk(u) < len(q)-1:
                    continue
                reduced_t = splice(t, q, u)
                result, residual = exterior(middle, q, u)
                direct_tree, direct = exterior(outer, first, reduced_t)
                assert direct_tree == result
                ctx = tree_ctx(result)
                first_head = ('coh', tree_ctx(middle), after_first, residual)
                second_head = subst_tm(original, direct)
                left_bound = subst_ty(after_first, residual)
                right_bound = subst_ty(original[2], direct)
                left_head = ('coh', ctx, left_bound, variables(ctx))
                right_head = ('coh', ctx, right_bound, variables(ctx))
                b = max(d-j, height(u)-trunk(u))
                checks = programs.setdefault(b, Assertions())
                checks.equal(ctx, first_head, left_head, 'residual insertion')
                checks.equal(ctx, second_head, right_head, 'merged insertion')
                checks.equal(ctx, left_head, right_head, 'transported head types')
    total = 0
    with TemporaryDirectory() as tmp:
        program = Path(tmp)/'Nested.catt'
        for b, checks in programs.items():
            program.write_text('\n'.join(checks.commands)+'\n')
            result = subprocess.run([binary, '--insertion-width', str(b), program],
                                    text=True, capture_output=True, check=True)
            expected = sum(checks.count.values())
            if result.stdout.count('are equal') != expected or result.stderr:
                raise AssertionError((b, result.stderr[-2000:], result.stdout[-2000:]))
            total += expected
    print(f'{total} typed nested-join comparisons at the original width bounds')


def check_old_boundary(binary):
    # The shallow first column disappears on scalars. On the loop tower it stays.
    inner = ((), ((), ()))
    generic, tower, *_ = template_cases(inner)
    outer = glue_tree(2, 0, 2)
    ctx = tree_ctx(splice(outer, (0,), inner))
    code = Assertions()
    corr = head(ctx, generic.right, generic.left)
    sigma = tuple(v(tdim(ty)+1) for ty in ctx)
    repair = code.term(subst_tm(corr, sigma))
    nested, flat = code.term(tower.left), code.term(tower.right)
    extension = f'{tower.context} (p : {nested} -> {nested})'
    written = f'{flat} -> {nested}'
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder/'Heads.catt').write_text('\n'.join(code.commands)+'\n')
        for name, term in [('fitted', f'comp[{repair},p]'), ('direct', 'p')]:
            (folder/f'{name}.catt').write_text(
                f'import Heads\ndef {name} {extension} : {written} = {term}\n')
        accepted(run(binary, folder, 'fitted.catt'), 'fitted.catt', ['fitted'])
        rejected(run(binary, folder, 'direct.catt'), 'direct.catt', 'direct')
        for b in range(3):
            output = run(binary, folder, 'direct.catt', ['--insertion-width', str(b)])
            if b < tower.width:
                rejected(output, 'direct.catt', 'direct')
            else:
                accepted(output, 'direct.catt', ['direct'])
    print('Mixed-rank generator: raw boundary repair and least direct-use width 2')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('binary', type=Path, help='checker built by semistrict_surface_bounded_rice.py')
    parser.add_argument('--edges', type=int, default=5)
    args = parser.parse_args()
    check_residuals(args.edges)
    check_queries(args.binary.resolve(), args.edges)
    check_nested(args.binary.resolve())
    check_old_boundary(args.binary.resolve())
