"""Check fresh-target expansion and its two serial comparisons at composite lower poles."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import STAR, arr, comp2, disc_tree, glue_tree, infer, maximal_vars, sub_from, subst_tm, subst_ty, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, rejected, run


def compare_schedules(ctx, rank, left, right):
    """The unbiased pair of steps and the two possible serial pastes have the same faces."""
    arity = tree_ctx(glue_tree(rank + 1, rank - 1, rank + 1))
    slots = maximal_vars(arity)
    p, q = map(v, slots)
    sigma = sub_from(arity, ctx, dict(zip(slots, (left, right))))
    both = comp2(arity, rank - 1, p, q)
    first = (comp2(arity, rank - 1, p, infer(arity, q)[2]),
             comp2(arity, rank - 1, infer(arity, p)[3], q))
    second = (comp2(arity, rank - 1, infer(arity, p)[2], q),
              comp2(arity, rank - 1, p, infer(arity, q)[3]))
    for steps in (first, second):
        serial = comp2(arity, rank, *steps)
        yield tuple(subst_tm(t, sigma) for t in (both, serial, head(arity, both, serial)))


def check_pairs(n, dual, emitter):
    # The two lower arrows are composable loops but are distinct generators.
    # The n-variable w has a composite lower pole, and b has no top input.
    base = (STAR,)
    pole = v(0)
    for _ in range(n - 2):
        lower_ty = arr(infer(base, pole), pole, pole)
        pole = v(len(base))
        base += (lower_ty,)
    lower_ty = arr(infer(base, pole), pole, pole)
    f, g = v(len(base)), v(len(base) + 1)
    base += (lower_ty, lower_ty)
    fg = comp2(base, n - 2, f, g)
    p, q, w = map(v, range(len(base), len(base) + 3))
    w_ty = arr(infer(base, fg), fg, fg)
    base += (arr(lower_ty, f, f), arr(lower_ty, g, g), w_ty)
    pq = comp2(base, n - 2, p, q)
    empty = identity(base, fg)
    ww = comp2(base, n - 1, w, w)

    def rule(source, target):
        return arr(w_ty, target, source) if dual else arr(w_ty, source, target)

    first, birth, merge = map(v, range(len(base), len(base) + 3))
    ctx = base + tuple(rule(s, w) for s in (pq, empty, ww))
    copied = base
    fold = list(map(v, range(len(base))))
    expand = fold.copy()

    def attach(s, old_rule):
        nonlocal copied
        t, z = v(len(copied)), v(len(copied) + 1)
        image = subst_tm(s, expand)
        copied += (w_ty, rule(s, t))
        fold.extend((w, old_rule))
        expand.extend((image, identity(base, image)))
        return t, z

    a, za = attach(pq, first)
    b, zb = attach(empty, birth)
    c, zc = attach(comp2(copied, n - 1, a, b), merge)
    for i, ty in enumerate(copied):
        assert infer(ctx, fold[i]) == subst_ty(ty, fold[:i])
        assert infer(base, expand[i]) == subst_ty(ty, expand[:i])
    schedules = []
    for index, (both, serial, comparison) in enumerate(compare_schedules(copied, n, za, zb)):
        def through_root(term):
            return comp2(copied, n, zc, term) if dual else comp2(copied, n, term, zc)

        full, linear, witness = map(through_root, (both, serial, comparison))
        assert infer(copied, witness)[2:] == (full, linear)
        assert infer(copied, full)[2:] == ((c, expand[c[1]]) if dual else (expand[c[1]], c))
        tag = f'{"split" if dual else "merge"}{n}schedule{index}'
        emitter.check_type(tag, copied, witness, arr(infer(copied, full), full, linear))
        for label, target_ctx, assignment in [('Fold', ctx, fold), ('Expand', base, expand)]:
            path = subst_tm(witness, assignment)
            expected_ty = subst_ty(infer(copied, witness), assignment)
            assert infer(target_ctx, path) == expected_ty
            emitter.check_type(tag + label, target_ctx, path, expected_ty)
        schedules.append(linear)
    assert schedules[0] != schedules[1]

    # Subdivide a rule with composites on both sides, then return along
    # the left unitor at its exact original faces.
    if not dual:
        target = comp2(base, n - 1, pq, empty)
        original = base + (rule(ww, target),)
        mid, enter, leave = map(v, range(len(base), len(base) + 3))
        split = base + (w_ty, rule(ww, mid), rule(mid, target))
        composite = comp2(split, n, enter, leave)
        z = v(len(base))
        back = list(map(v, range(len(base)))) + [ww, identity(base, ww), z]
        returned = subst_tm(composite, back)
        disc = tree_ctx(disc_tree(n + 1))
        top = v(maximal_vars(disc)[0])
        padded = comp2(disc, n, identity(disc, infer(disc, top)[2]), top)
        unitor = subst_tm(head(disc, padded, top), sub_from(disc, original, {top[1]: z}))
        emitter.check_type(f'subdivided{n}', split, composite, rule(ww, target))
        emitter.check_type(f'returned{n}', original, unitor, arr(infer(original, z), returned, z))


def check_rice(checkout):
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as directory:
        root = Path(directory)
        (root / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        for dual in (False, True):
            def directed(source, target):
                return f'{target} -> {source}' if dual else f'{source} -> {target}'

            fg = 'comp[f,g]'
            prefix = (f'(x : *) (f : x -> x) (g : x -> x) (p : f -> f) (q : g -> g) '
                      f'(a : {fg} -> {fg}) (b : {fg} -> {fg}) (c : {fg} -> {fg})')
            pq = 'comp[[p],[q]]'
            unit = f'id({fg})'
            ctx = (f'{prefix} (u : {directed(pq, "a")}) (v : {directed(unit, "b")}) '
                   f'(z : {directed("comp[a,b]", "c")})')
            ends = directed(f'comp[{pq},{unit}]', 'c')
            direct = 'comp[z,comp[[u],[v]]]' if dual else 'comp[comp[[u],[v]],z]'
            use = 'path(x,f,g,p,q,a,b,c,u,v,z)'
            endpoint = f'comp[{pq},{unit}]' if dual else 'c'
            pad = f'comp[{use},id({endpoint})]'
            (root / 'Raw.catt').write_text(f"""import examples/eh-common
def path {ctx} : {ends} = {direct}
def fit {ctx} : {use} -> {pad} = unitor_r_inv({use})
""")
            (root / 'Exact.catt').write_text(f'import Raw\ndef exact {ctx} : {use} -> {pad} = id({use})\n')
            (root / 'Wrong.catt').write_text(f'import Raw\ndef wrong {ctx} : {directed("comp[b,a]", "c")} = z\n')
            for flags in ([], ['--su'], ['--sua']):
                accepted(run(binary, root, 'Raw.catt', flags), 'Raw.catt', ['path', 'fit'])
                check = run(binary, root, 'Exact.catt', flags)
                if flags:
                    accepted(check, 'Exact.catt', ['exact'])
                else:
                    rejected(check, 'Exact.catt', 'exact')
                rejected(run(binary, root, 'Wrong.catt', flags), 'Wrong.catt', 'wrong')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    for rank in (2, 3, 4):
        for reverse in (False, True):
            check_pairs(rank, reverse, emitter)
    if args.agda_dir:
        module = 'FreshTargetComparisons'
        (args.agda_dir / (module + '.agda')).write_text(emitter.module(module, __doc__))
    print('Checked 12 higher comparisons and their 24 folded or expanded images.')
    print('Checked three two-sided subdivisions and their raw return unitors.')
    check_rice(args.checkout.resolve())
    print('Checked exact raw and converted boundaries and incompatible port orders in both orientations.')
