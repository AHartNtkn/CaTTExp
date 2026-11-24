"""Check absolute seam intersections, compatibility with pruning and a mixed raw boundary."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import permutations
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import STAR, arr, comp2, disc_tree, glue_tree, infer, maximal_vars, sub_from, subst_tm, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from partial_cylinder_steiner import trees
from relative_coherence_exchange_faces import head, string_tree
from semistrict_surface_elementary_insertions import exterior, slots
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_insertion_cut import Assertions, ucomp
from semistrict_surface_peak_sections import prune


def neighbor(path, displacement):
    return path[:-1] + (path[-1] + displacement,)


def drop(path, omitted):
    depth = len(omitted) - 1
    if len(path) > depth and path[:depth] == omitted[:depth] and path[depth] > omitted[depth]:
        return path[:depth] + (path[depth] - 1,) + path[depth + 1:]
    return path


@cache
def erase(tree, path):
    return exterior(tree, path, disc_tree(len(path) - 1))


@cache
def merge(tree, path):
    small = prune(tree, neighbor(path, 1))
    restored, include = exterior(small, path, glue_tree(len(path), len(path) - 1, len(path)))
    assert restored == tree
    return small, include


def then(first, second):
    return tuple(subst_tm(t, second) for t in first)


def shape_checks(edges):
    checks, counts = Assertions(), Counter()
    tested = set()

    def compare(target, actual, expected, name):
        assert len(actual) == len(expected)
        for l, r in zip(actual, expected, strict=True):
            if l != r and (target, l, r) not in tested:
                tested.add((target, l, r))
                checks.equal(tree_ctx(target), l, r, name)
        counts[name] += 1

    for n in range(1, edges + 1):
        for tree in trees(n):
            peaks = slots(tree)
            seams = [p for p in peaks if neighbor(p, 1) in peaks]
            for i in seams:
                smaller, ki = merge(tree, i)
                for tip in peaks:
                    residual, q = erase(tree, tip)
                    if tip in (i, neighbor(i, 1)):
                        assert smaller == residual
                        compare(residual, then(ki, q), tuple(map(v, range(len(tree_ctx(smaller))))),
                                'endpoint retractions')
                    else:
                        last, k_after = merge(residual, drop(i, tip))
                        first, q_before = erase(smaller, drop(tip, neighbor(i, 1)))
                        assert first == last
                        compare(residual, then(ki, q), then(q_before, k_after), 'other tip squares')
            for i, j in permutations(seams, 2):
                small_i, ki = merge(tree, i)
                small_j, kj = merge(tree, j)
                j_after = drop(j, neighbor(i, 1))
                if j == neighbor(i, 1):
                    j_after = i
                i_after = drop(i, neighbor(j, 1))
                if i == neighbor(j, 1):
                    i_after = j
                both, lj = merge(small_i, j_after)
                twice, li = merge(small_j, i_after)
                assert both == twice
                compare(tree, then(lj, ki), then(li, kj), 'seam squares')
                killed = neighbor(i, 1) if i == neighbor(j, 1) else i
                residual, qi = erase(tree, killed)
                assert residual == small_i
                # The retracted other exterior already skips the residual seam.
                raw = then(kj, qi)
                for t in (j_after, neighbor(j_after, 1)):
                    core, qj = erase(small_i, t)
                    assert core == both
                    compare(small_i, then(then(raw, qj), lj), raw, 'protected seam images')
                if j in (neighbor(i, -1), neighbor(i, 1)) and len(i) == len(j):
                    counts['adjacent triples'] += 1
    return checks, counts


def mixed(binary, directory):
    d = 3
    base = glue_tree(d, 0, d)
    a, c = sorted(slots(base))
    small, _ = exterior(base, a, glue_tree(d, d - 1, d))
    wide, _ = exterior(base, c, glue_tree(d, d - 1, d))
    # A left-folded first column and a two-slot second column, one labelled
    # by the identity, are compared with the generic first-column split.
    joined, inc_a = exterior(wide, a, glue_tree(d, d - 1, d))
    back, q = erase(joined, c)
    assert back == small
    ctx = tree_ctx(small)
    lhs = subst_tm(ucomp(tree_ctx(wide)), then(inc_a, q))
    rhs = ucomp(ctx)
    assert infer(ctx, lhs) == infer(ctx, rhs) and lhs != rhs
    corr = head(ctx, rhs, lhs)
    point = (STAR,)
    pole = v(0)
    for _ in range(d - 1):
        pole = ident(point, pole)
    scalar = point + (arr(infer(point, pole), pole, pole),)
    sigma = sub_from(ctx, scalar, dict.fromkeys(maximal_vars(ctx), v(1)))
    left, right, correction = (subst_tm(t, sigma) for t in (lhs, rhs, corr))
    full = scalar + (arr(infer(scalar, left), left, left),)
    direct = v(2)
    fitted = comp2(full, d, correction, direct)
    old_type = arr(infer(full, right), right, left)
    assert infer(full, fitted) == old_type and infer(full, direct) != old_type
    if directory:
        directory.mkdir(parents=True, exist_ok=True)
        emitter = Emitter()
        emitter.check_typed('fitted', full, fitted)
        emitter.check_type('fitted-old-type', full, fitted, old_type)
        name = 'MixedTemporalInsertion'
        (directory / (name + '.agda')).write_text(emitter.module(name, __doc__))
    if binary:
        with TemporaryDirectory() as tmp:
            folder = Path(tmp)
            writer = Assertions()
            def show(ty):
                return '*' if ty == STAR else ' -> '.join(map(writer.term, ty[2:]))
            declarations = ' '.join(f'(x{i} : {show(ty)})' for i, ty in enumerate(full))
            definitions = {name: f'def {name} {declarations} : {show(old_type)} = {writer.term(term)}'
                           for name, term in (('direct', direct), ('fitted', fitted))}
            (folder / 'Heads.catt').write_text('\n'.join(writer.commands) + '\n')
            for name, command in definitions.items():
                (folder / f'{name}.catt').write_text(f'import Heads\n{command}\n')
            accepted(run(binary, folder, 'fitted.catt'), 'fitted.catt', ['fitted'])
            rejected(run(binary, folder, 'direct.catt', ['--su']), 'direct.catt', 'direct')
            accepted(run(binary, folder, 'direct.catt', ['--insertion-width', '1']), 'direct.catt', ['direct'])
    print('Mixed head with a temporal split, an identity tip, and a 4-generator at the written boundary')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--edges', type=int, default=6)
    parser.add_argument('--rice-binary', type=Path)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    checks, counts = shape_checks(args.edges)
    print(dict(counts), flush=True)
    if args.rice_binary:
        with TemporaryDirectory() as tmp:
            folder = Path(tmp)
            (folder / 'Implications.catt').write_text('\n'.join(checks.commands) + '\n')
            result = run(args.rice_binary, folder, 'Implications.catt', ['--insertion-width', '1'])
            assert result.count('are equal') == sum(checks.count.values()), result[-1500:]
            print(f'{sum(checks.count.values())} nonliteral coordinate equations in width one')
    mixed(args.rice_binary, args.agda_dir)
