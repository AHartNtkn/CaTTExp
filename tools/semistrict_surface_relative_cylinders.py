"""Check rank-bounded naturality on a partial cylinder with a converted generic face."""
from argparse import ArgumentParser
from functools import cache
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, comp2, disc_tree, glue_tree, is_ps, maximal_vars, subst_tm,
                  subst_ty, tdim, tree_ctx, ucomp, v)
from ct_suspension import ident
from relative_coherence_cut import top_counts
from semistrict_surface_exact_boundary import accepted, run
from semistrict_surface_insertion_cut import Assertions
from semistrict_surface_rank_cut import RankCut


@cache
def ty(ctx, cell):
    return ctx[cell[1]] if cell[0] == 'v' else subst_ty(cell[2], cell[3])


def source(ctx, cell):
    return ty(ctx, cell)[2]


def target(ctx, cell):
    return ty(ctx, cell)[3]


def direct(ctx, a, b):
    return ('coh', ctx, arr(ty(ctx, a), a, b), tuple(map(v, range(len(ctx)))))


def apply(arity, term, ctx, labels):
    # Choose one writing at each shared position. RankCut verifies *all* its incidences.
    entries = dict(zip(maximal_vars(arity), labels, strict=True))
    for i in reversed(range(len(arity))):
        if arity[i] == STAR:
            continue
        actual = ty(ctx, entries[i])
        for var, endpoint in zip(arity[i][2:], actual[2:], strict=True):
            entries.setdefault(var[1], endpoint)
    return subst_tm(term, tuple(entries[i] for i in range(len(arity))))


def compose(ctx, cut, a, b):
    dims = [tdim(ty(ctx, x)) + 1 for x in (a, b)]
    arity = tree_ctx(glue_tree(dims[0], cut, dims[1]))
    return apply(arity, ucomp(arity), ctx, [a, b])


def seq(ctx, a, b):
    return compose(ctx, tdim(ty(ctx, a)), a, b)


@cache
def templates():
    three, four, five = (tree_ctx(disc_tree(i)) for i in (3, 4, 5))
    x = v(maximal_vars(three)[0])
    lower = source(three, x)
    padded = comp2(three, 1, lower, ident(three, target(three, lower)))
    p = direct(three, padded, target(three, x))
    j = direct(three, x, p)  # Its two 3-faces have different written 2-sources.
    f = v(maximal_vars(four)[0])
    a, b = ty(four, f)[2:]
    d = direct(four, a, apply(three, p, four, [b]))
    pf = direct(four, apply(three, p, four, [a]), apply(three, p, four, [b]))

    def df(ctx, edge):
        return apply(four, d, ctx, [edge])

    def shifted(ctx, edge):
        return seq(ctx, edge, apply(three, j, ctx, [target(ctx, edge)]))

    align = direct(four, shifted(four, f), d)
    tile = v(maximal_vars(five)[0])
    u, w = ty(five, tile)[2:]
    dt = direct(five, df(five, u), df(five, w))
    whisker = compose(five, 3, tile, apply(three, j, five, [target(five, u)]))
    l = seq(five, whisker, apply(four, align, five, [w]))
    r = seq(five, apply(four, align, five, [u]), dt)

    row = tree_ctx(glue_tree(4, 3, 4))
    a, b = map(v, maximal_vars(row))
    ab = seq(row, a, b)
    old = seq(row, df(row, a), apply(four, pf, row, [b]))
    new = seq(row, a, df(row, b))
    first = direct(row, old, shifted(row, ab))
    last = direct(row, df(row, ab), new)
    return three, j, row, first, last, five, l, r, direct(five, l, r), direct(five, r, l)


def square():
    prefix = tree_ctx(disc_tree(3))[:-1]  # The common 2-boundary.
    typ = tree_ctx(disc_tree(3))[-1]
    ctx = prefix + (typ,) * 4
    a, b, aa, bb = (v(len(prefix)+i) for i in range(4))

    def edge(x, y):
        nonlocal ctx
        t = v(len(ctx))
        ctx += (arr(typ, x, y),)
        return t

    old, ea, eb, new = edge(a, b), edge(a, aa), edge(b, bb), edge(aa, bb)
    w, ww = seq(ctx, old, eb), seq(ctx, ea, new)
    tile = v(len(ctx))
    return ctx + (arr(ty(ctx, w), w, ww),), old, ea, eb, new, tile


def check(binary, folder):
    three, j, row, first, last, five, l, r, forward, backward = templates()
    ctx, old, ea, eb, new, tile = square()
    assert not is_ps(ctx)
    first = apply(row, first, ctx, [old, eb])
    last = apply(row, last, ctx, [ea, new])
    l, r, f, b = [apply(five, t, ctx, [tile]) for t in (l, r, forward, backward)]

    def border(t):
        return seq(ctx, seq(ctx, first, t), last)

    def carry(t):
        return compose(ctx, 4, compose(ctx, 4, first, t), last)

    left, right = border(l), border(r)
    f, b = carry(f), carry(b)
    low = RankCut(1, binary, folder)
    assert not low.equal_type(three, ty(three, source(three, j)), ty(three, target(three, j)))
    high = RankCut(2, binary, folder)
    assert high.checks(three, j, ty(three, j))
    assert high.checks(ctx, f, arr(ty(ctx, left), left, right))
    assert high.checks(ctx, b, arr(ty(ctx, right), right, left))
    assert not high.equal_term(ctx, left, right)
    assert top_counts(ctx, left) == top_counts(ctx, right) == {tile[1]: 1}

    writer = Assertions()
    decls = []
    for i, typ in enumerate(ctx):
        written = '*' if typ == STAR else f'{writer.term(typ[2])} -> {writer.term(typ[3])}'
        decls.append(f'(x{i} : {written})')
    lterm, rterm = writer.term(left), writer.term(right)
    lines = [f'def {name} {" ".join(decls)} : {s} -> {t} = {writer.term(witness)}'
             for name, s, t, witness in [('forward', lterm, rterm, f), ('backward', rterm, lterm, b)]]
    name = 'RelativeCylinder.catt'
    (folder / name).write_text('\n'.join([*writer.commands, *lines]) + '\n')
    accepted(run(binary, folder, name, ['--sua']), name, ['forward', 'backward'])
    print('Nonglobular square: two distinct rank-two readings, one tile each, both six-cell '
          'comparisons checked at cap two and in the published checker; rank one separates the face types.')


def check_units(binary, folder):
    for rank in (1, 2, 3):
        # The first factor is stationary. Only the second one changes.
        arity = tree_ctx(glue_tree(rank, rank - 1, rank + 1))
        fixed, change = map(v, maximal_vars(arity))
        lo = seq(arity, fixed, source(arity, change))
        hi = seq(arity, fixed, target(arity, change))
        lift = direct(arity, lo, hi)
        disc = tree_ctx(disc_tree(rank + 1))
        moving = v(maximal_vars(disc)[0])
        unit = ident(disc, source(disc, source(disc, moving)))
        specialized = apply(arity, lift, disc, [unit, moving])
        cap = RankCut(rank, binary, folder)
        assert cap.checks(arity, lift, ty(arity, lift))
        assert not cap.equal_type(arity, ty(arity, lift), ty(arity, change))
        assert cap.checks(disc, specialized, ty(disc, moving))
        assert not cap.equal_term(disc, specialized, moving)
        print(f'Cap {rank}: the unit specialization has the variable’s boundary and a distinct constructor.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('binary', type=Path)
    args = parser.parse_args()
    with TemporaryDirectory() as scratch:
        check(args.binary.resolve(), Path(scratch))
        check_units(args.binary.resolve(), Path(scratch))
