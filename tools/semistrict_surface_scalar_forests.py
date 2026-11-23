"""Check occurrence trees and raw parallel paths for a scalar merger and a birth."""
from argparse import ArgumentParser
from functools import cache
from itertools import permutations
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import STAR, arr, comp2, infer, maximal_vars, sub_from, subst_tm, subst_ty, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_weight_cut import depth_slots


@cache
def occurrences(term, rank):
    if term[0] == 'v':
        return (term[1],)
    _, arity, _, args = term
    return tuple(i for _, (slot,), _ in depth_slots(arity, rank)
                 for i in occurrences(args[slot], rank))


def evaluate(ctx, rank, term, initial):
    ty = infer(ctx, term)
    assert len(initial) == len(occurrences(ty[2], rank))
    if term[0] == 'v':
        return ((term[1], *initial),)
    _, arity, boundary, args = term
    states = {}
    rest = list(initial)
    for slot in occurrences(boundary[2], rank):
        width = len(occurrences(args[slot], rank))
        states[slot], rest = tuple(rest[:width]), rest[width:]
    assert not rest
    for local, slots, _ in depth_slots(arity, rank):
        for j, cell_type in enumerate(local):
            if cell_type == STAR:
                continue
            source = slots[cell_type[2][1]]
            target = slots[cell_type[3][1]]
            states[target] = evaluate(ctx, rank, args[slots[j]], states[source])
    result = tuple(x for slot in occurrences(boundary[3], rank) for x in states[slot])
    assert len(result) == len(occurrences(ty[3], rank))
    return result


def check_raw(emitter):
    count = 0
    for n in (2, 3, 4):
        unit = v(0)
        point = (STAR,)
        for _ in range(n - 1):
            unit = identity(point, unit)
        scalar_type = arr(infer(point, unit), unit, unit)
        a = v(1)
        ctx = point + (scalar_type,)
        pair = comp2(ctx, n - 1, a, a)
        ctx += (arr(scalar_type, pair, a), arr(scalar_type, identity(ctx, unit), a))
        merge, birth = v(2), v(3)
        three = tree_ctx(string_tree(n - 1, [n, n, n]))
        x, y, z = map(v, maximal_vars(three))
        first = comp2(three, n - 1, comp2(three, n - 1, x, y), z)
        last = comp2(three, n - 1, x, comp2(three, n - 1, y, z))
        sigma = sub_from(three, ctx, dict.fromkeys(maximal_vars(three), a))
        reassociate = subst_tm(head(three, first, last), sigma)
        left_merge = comp2(ctx, n, comp2(ctx, n - 1, merge, a), merge)
        right_merge = comp2(ctx, n, reassociate, comp2(ctx, n, comp2(ctx, n - 1, a, merge), merge))
        assert infer(ctx, left_merge) == infer(ctx, right_merge)
        for leaves in permutations(('u', 'v', 'w')):
            x, y, z = leaves
            assert evaluate(ctx, n, left_merge, leaves) == ((2, (2, x, y), z),)
            assert evaluate(ctx, n, right_merge, leaves) == ((2, x, (2, y, z)),)
            count += 2
        with_birth = comp2(ctx, n, comp2(ctx, n - 1, a, birth), merge)
        assert evaluate(ctx, n, with_birth, ('u',)) == ((2, 'u', (3,)),)
        empty = comp2(ctx, n, comp2(ctx, n - 1, birth, birth), merge)
        assert evaluate(ctx, n, empty, ()) == ((2, (3,), (3,)),)
        emitter.check_type(f'rightMerge{n}', ctx, right_merge, infer(ctx, left_merge))
        emitter.check_type(f'emptyForest{n}', ctx, empty, infer(ctx, empty))
        # Lift the repeated rule at specific ordered input trees. Read each
        # tree as an actual composite of its leaves in the pure context.
        pure = point + (scalar_type,) * 3
        copied = pure
        expand = list(map(v, range(4)))
        fold = [v(0), a, a, a]

        def attach(inputs):
            nonlocal copied
            if inputs:
                source = comp2(copied, n - 1, *inputs)
                rule = merge
            else:
                source = identity(copied, unit)
                rule = birth
            label = v(len(copied))
            arrow = v(len(copied) + 1)
            leaves = subst_tm(source, expand)
            copied += (scalar_type, arr(scalar_type, source, label))
            expand.extend((leaves, identity(pure, leaves)))
            fold.extend((a, rule))
            return label, arrow

        xy, mxy = attach((v(1), v(2)))
        xyz, mxyz = attach((xy, v(3)))
        null, e = attach(())
        null_pair, mnull = attach((null, null))
        for i, declaration in enumerate(copied):
            assert infer(ctx, fold[i]) == subst_ty(declaration, fold[:i])
            assert infer(pure, expand[i]) == subst_ty(declaration, expand[:i])
        lifted = comp2(copied, n, comp2(copied, n - 1, mxy, v(3)), mxyz)
        lifted_empty = comp2(copied, n, comp2(copied, n - 1, e, e), mnull)
        for name, path, end, old in [('merge', lifted, xyz, left_merge),
                                     ('birth', lifted_empty, null_pair, empty)]:
            assert infer(copied, path)[3] == end and subst_tm(path, fold) == old
            leaf_path = subst_tm(path, expand)
            assert infer(pure, leaf_path) == subst_ty(infer(copied, path), expand)
            assert infer(pure, leaf_path)[3] == expand[end[1]]
            emitter.check_eq(f'{name}Fold{n}', path, fold, old)
            emitter.check_type(f'{name}Leaf{n}', pure, leaf_path, subst_ty(infer(copied, path), expand))
        count += 2
    return count


def check_rice(checkout):
    exe = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as folder:
        root = Path(folder)
        (root / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        for n in (2, 3, 4):
            pole = 'x'
            for _ in range(n - 2):
                pole = f'id({pole})'
            unit = f'id({pole})'
            ctx = f'(x : *) (a : {unit} -> {unit}) (m : comp[a,a] -> a) (e : id({unit}) -> a)'
            args = 'x,a,m,e'
            swap = f'eh({pole},a,a)'
            (root / 'Forest.catt').write_text(f"""import examples/eh
def reassoc = coh [ [f,g,h] : comp[comp[f,g],h] -> comp[f,comp[g,h]] ]
def left {ctx} : comp[comp[a,a],a] -> a = comp[comp[[m],a],m]
def right {ctx} : comp[comp[a,a],a] -> a = comp[reassoc(a,a,a),comp[a,[m]],m]
def birth_merge {ctx} : comp[a,id({unit})] -> a = comp[comp[a,[e]],m]
def twice {ctx} : comp[a,a] -> a = comp[{swap},{swap},m]
def fitted {ctx} : twice({args}) -> comp[twice({args}),id(a)] = unitor_r_inv(twice({args}))
""")
            for test, a, b in [('shape', f'left({args})', f'right({args})'),
                               ('winding', f'twice({args})', 'm')]:
                (root / f'{test}.catt').write_text(f'import Forest\ndef {test} {ctx} : {a} -> {b} = id({a})\n')
            for flags in ([], ['--su'], ['--sua']):
                accepted(run(exe, root, 'Forest.catt', flags), 'Forest.catt',
                         ['left', 'right', 'birth_merge', 'twice', 'fitted'])
                for test in ('shape', 'winding'):
                    rejected(run(exe, root, f'{test}.catt', flags), f'{test}.catt', test)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    print(f'{check_raw(emitter)} typed forest evaluations.')
    if args.agda_dir:
        name = 'ScalarMergeForests'
        (args.agda_dir / f'{name}.agda').write_text(emitter.module(name, __doc__))
    check_rice(args.checkout.resolve())
    print('Checked merges, births, braid precomposition and identity controls in all three modes.')
