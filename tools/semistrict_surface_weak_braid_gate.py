"""Check the typed two-rule construction and its four-dimensional cube obstruction."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import arr, check_ctx, comp2, disc_tree, infer, src, tgt, tree_ctx, v
from emit_agda import Emitter
from gray_globe_comparison import atom, boundary
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, run
from semistrict_surface_first_failure_gate import compare_on_disc, unchanged
from semistrict_surface_odd_cubes import EDGE


def check_cube():
    cube = (EDGE,) * 4
    before, after = atom(cube)[3]
    assert len(before) == len(after) == 4 and set(before).isdisjoint(after)
    delta = boundary(cube)
    assert delta == {**dict.fromkeys(before, -1), **dict.fromkeys(after, 1)}
    # There is one basis element in degree four. Any reverse would have
    # coefficient -1, read off at any one of these eight distinct facets.
    for facet in (*before, *after):
        assert (before.count(facet) - after.count(facet)) == -delta[facet]


def check_attachments():
    # Instantiate the construction at general parallel 4-faces. The two
    # sufficient hypotheses are supplied in separate extended contexts.
    ctx = tree_ctx(disc_tree(4))
    p, q = v(len(ctx) - 1), v(len(ctx))
    ctx += (ctx[-1],)

    def declare(ty):
        nonlocal ctx
        name = v(len(ctx))
        ctx += (ty,)
        return name

    def rule(source, target):
        assert infer(ctx, source) == infer(ctx, target)
        return declare(arr(infer(ctx, source), source, target))

    f = tgt(ctx, tgt(ctx, tgt(ctx, p)))
    unit = identity(ctx, f)
    red, green, blue = [rule(unit, unit) for _ in range(3)]
    base = comp2(ctx, 2, comp2(ctx, 2, red, green), blue)
    c, d, word = [rule(base, base) for _ in range(3)]
    change = rule(c, d)
    composite = comp2(ctx, 3, word, c)
    start, finish = comp2(ctx, 1, p, c), comp2(ctx, 1, q, d)
    middle = comp2(ctx, 1, p, composite)
    gate = rule(middle, finish)
    check_ctx(ctx)
    em = Emitter()
    expected = arr(infer(ctx, start), start, finish)
    em.check_type('attaching', ctx, gate, arr(infer(ctx, start), middle, finish))

    ctx_base = ctx
    cube_reverse = rule(p, q)
    surface_branch = comp2(ctx, 1, cube_reverse, change)
    assert infer(ctx, surface_branch) == expected
    em.check_type('reverse-and-change', ctx, surface_branch, expected)

    ctx = ctx_base
    reduction = rule(identity(ctx, base), word)

    def left_unit(context, term):
        return comp2(context, 3, identity(context, src(context, term)), term)

    unit_fit = compare_on_disc(ctx, c, unchanged, left_unit)
    insert_word = comp2(ctx, 4, unit_fit, comp2(ctx, 3, reduction, c))
    witness = comp2(ctx, 4, comp2(ctx, 1, p, insert_word), gate)
    assert infer(ctx, witness) == expected
    em.check_type('word-reduction-and-gate', ctx, witness, expected)
    return em


def check_coloured_loops(checkout):
    context = '(x : *) ' + ' '.join(f'({name} : id(x) -> id(x))' for name in ('a', 'b', 'c'))
    base = 'comp[comp[a,b],c]'
    with TemporaryDirectory() as temp:
        directory = Path(temp)
        (directory / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        # Read both adjacent full twists at exactly the same triple composite.
        (directory / 'Twists.catt').write_text(f"""import examples/eh
def bracket = coh [[f,g,h] : comp[comp[f,g],h] -> comp[f,comp[g,h]]]
def unbracket = coh [[f,g,h] : comp[f,comp[g,h]] -> comp[comp[f,g],h]]
def twice (x : *) (a : id(x) -> id(x)) (b : id(x) -> id(x))
  = comp[eh(x,a,b),eh(x,b,a)]
def leftloop {context} : {base} -> {base} = comp[[twice(x,a,b)],c]
def rightloop {context} : {base} -> {base}
  = comp[bracket(a,b,c),comp[a,[twice(x,b,c)]],unbracket(a,b,c)]
""")
        output = run(checkout / 'target/release/catt_strict', directory, 'Twists.catt')
        accepted(output, 'Twists.catt', ('leftloop', 'rightloop'))
    print('Rice checked both pure twists at the common three-colour base.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    parser.add_argument('--rice', type=Path)
    args = parser.parse_args()
    if args.rice:
        check_coloured_loops(args.rice.resolve())
    check_cube()
    emitter = check_attachments()
    if args.agda_dir:
        module = 'GrayWeakBraidGate'
        body = emitter.module(module, __doc__).replace('open import CaTTExp.Pure',
                                                       'open import CaTTExp.Gray.Pure')
        (args.agda_dir / (module + '.agda')).write_text(body)
    print('Eight oriented facets and both fitted witnesses at the same old 5-type checked.')
