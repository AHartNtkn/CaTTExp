"""Check degree-six naturality for a nested temporal action and a spatial insertion."""
from argparse import ArgumentParser
from functools import cache
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, chain_tree, comp2, disc_tree, glue_tree, infer,
                  maximal_vars, src, sub_from, subst_tm, tdim, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident
from relative_coherence_exchange_faces import head
from semistrict_surface_equal_rank import suspend
from semistrict_surface_exact_boundary import accepted, run
from semistrict_surface_grid_tracks import temporal
from semistrict_surface_insertion_cut import Assertions
from semistrict_surface_insertion_tracks import insert
from semistrict_surface_rank_cut import RankCut


RANK = 3


@cache
def chart(history):
    # Three successive rank-three inputs, each with its own copy of the history.
    return tree_ctx(suspend((history,) * 3, RANK - 1))


def apply(arity, operation, ctx, labels):
    sigma = sub_from(arity, ctx, dict(zip(maximal_vars(arity), labels, strict=True)))
    return subst_tm(operation, sigma)


@cache
def roots():
    p = chart(())
    x, y, z = map(v, maximal_vars(p))
    return ucomp(p), temporal(p, temporal(p, x, y), z)


@cache
def action(degree, g, h):
    p = chart(disc_tree(degree))
    top = list(map(v, maximal_vars(p)))
    minus, plus = ([face(p, x) for x in top] for face in (src, tgt))
    domain = chart(disc_tree(degree - 1))
    if degree == 1:
        lo, hi = roots()[g], roots()[h]
    else:
        lo = hi = action(degree - 1, g, h)
    return head(p, apply(domain, lo, p, minus), apply(domain, hi, p, plus))


@cache
def compositor(g, h, j):
    p = chart(chain_tree(2))
    slots = list(map(v, maximal_vars(p)))
    first, second = slots[::2], slots[1::2]
    arrows = chart(disc_tree(1))
    left = temporal(p, apply(arrows, action(1, g, h), p, first),
                    apply(arrows, action(1, h, j), p, second))
    merged = [temporal(p, a, b) for a, b in zip(first, second, strict=True)]
    return head(p, left, apply(arrows, action(1, g, j), p, merged))


def naturality():
    p = chart(glue_tree(2, 0, 2))
    slots = list(map(v, maximal_vars(p)))
    pairs = list(zip(slots[::2], slots[1::2], strict=True))
    squares = chart(disc_tree(2))
    first, second = (apply(squares, action(2, g, h), p, slots[k::2])
                     for k, g, h in ((0, 0, 1), (1, 1, 0)))
    horizontal = comp2(p, RANK, first, second)
    merged = apply(squares, action(2, 0, 0), p, [comp2(p, RANK, a, b) for a, b in pairs])

    def at(face):
        return apply(chart(chain_tree(2)), compositor(0, 1, 0), p, [face(p, x) for x in slots])

    left = temporal(p, horizontal, at(tgt))
    right = temporal(p, at(src), merged)
    return p, left, right, head(p, left, right), head(p, right, left)


def splice_naturality():
    """Compare first acting in the inner head with acting on the spliced tree."""
    pair_tree = glue_tree(RANK, 0, RANK)
    pair = tree_ctx(pair_tree)
    joined_tree, _, joined_head, change = insert(ucomp(pair), pair_tree, (0,), pair_tree)
    joined = tree_ctx(joined_tree)

    @cache
    def spatial(n, degree):
        return tree_ctx((disc_tree(RANK + degree - 1),) * n)

    @cache
    def carrier(n, degree):
        if degree == 0:
            return ucomp(pair) if n == 2 else joined_head
        p = spatial(n, degree)
        top = list(map(v, maximal_vars(p)))
        below = spatial(n, degree - 1)
        h = carrier(n, degree - 1)
        return head(p, apply(below, h, p, [src(p, x) for x in top]),
                    apply(below, h, p, [tgt(p, x) for x in top]))

    def nested(degree):
        p = spatial(3, degree)
        x, y, z = map(v, maximal_vars(p))
        smaller, h = spatial(2, degree), carrier(2, degree)
        return apply(smaller, h, p, [apply(smaller, h, p, [x, y]), z])

    def at(p, arity, term, labels, face):
        return apply(arity, term, p, [face(p, x) for x in labels])

    arrows = spatial(3, 1)
    updates = list(map(v, maximal_vars(arrows)))
    lo = at(arrows, joined, change, updates, src)
    hi = at(arrows, joined, change, updates, tgt)
    square = head(arrows, temporal(arrows, nested(1), hi), temporal(arrows, lo, carrier(3, 1)))
    p = spatial(3, 2)
    bigons = list(map(v, maximal_vars(p)))
    # Each whisker uses the appropriate *vertex* copy of the splice track.
    after = at(p, arrows, hi, bigons, tgt)
    before = at(p, arrows, lo, bigons, src)
    left = temporal(p, comp2(p, RANK, nested(2), after), at(p, arrows, square, bigons, tgt))
    right = temporal(p, at(p, arrows, square, bigons, src), comp2(p, RANK, before, carrier(3, 2)))
    return p, left, right, head(p, left, right), head(p, right, left)


def spatial_change():
    tree = glue_tree(RANK, 0, RANK)
    joined, _, _, move = insert(ucomp(tree_ctx(tree)), tree, (0,), tree)
    p = tree_ctx(joined)
    back = head(p, tgt(p, move), src(p, move))

    def pad(t):
        return head(p, t, temporal(p, t, ident(p, tgt(p, t))))

    return p, pad(move), pad(back)


def check_weak_fit(binary, folder, ctx, face, fitted):
    writer = Assertions()
    declarations = []
    for i, ty in enumerate(ctx):
        written = '*' if ty == STAR else f'{writer.term(ty[2])} -> {writer.term(ty[3])}'
        declarations.append(f'(x{i} : {written})')
    pole = writer.term(face)
    query = f'def witness {" ".join(declarations)} : {pole} -> {pole} = {writer.term(fitted)}'
    name = 'NestedRaw.catt'
    (folder / name).write_text('\n'.join([*writer.commands, query]) + '\n')
    accepted(run(binary, folder, name), name, ['witness'])


def check(binary, folder):
    inner, alpha, beta = spatial_change()
    ctx = (STAR,)
    for i in range(RANK):
        ctx += (arr(ctx[-1], v(i), v(i)),)
    typ = ctx[-1]
    ctx += (typ, typ)
    raw = RankCut(0, binary, folder)
    published = RankCut(6, binary, folder)
    # Each child uses an independent loop, with all the object poles identified.
    labels = []
    for i in range(3):
        sigma = tuple(v(RANK + i if tdim(t) + 1 == RANK else tdim(t) + 1) for t in inner)
        labels.extend(subst_tm(t, sigma) for t in (alpha, beta))

    for case, diagram in (('temporal compositor', naturality), ('spatial splice', splice_naturality)):
        p, left, right, forward, backward = diagram()
        for external in (0, 1, 2):
            ambient = ctx
            actual = (labels if case == 'temporal compositor' else labels[::2]).copy()
            for i in range(external):
                variable = len(ambient)
                ambient += (infer(ctx, actual[i]),)
                actual[i] = v(variable)
            l, r, f, b = (apply(p, cell, ambient, actual) for cell in (left, right, forward, backward))
            assert l != r
            assert raw.checks(ambient, f, arr(infer(ambient, l), l, r))
            assert raw.checks(ambient, b, arr(infer(ambient, r), r, l))
            extension = ambient + (arr(infer(ambient, r), r, r),)
            z = v(len(ambient))
            fitted = temporal(extension, temporal(extension, f, z), b)
            expected = arr(infer(ambient, l), l, l)
            assert raw.checks(extension, fitted, expected)
            assert not raw.checks(extension, z, expected)
            check_weak_fit(binary, folder, extension, l, fitted)
            exact = case == 'spatial splice' or external < 2
            assert published.equal_term(ambient, l, r) == exact
            assert published.equal_term(extension, fitted, z) == exact
            print(f'{case}, {external} external 5-cells: weak fit checked, '
                  f'published routes and fits equal = {exact}')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('binary', type=Path, help='published catt_strict executable')
    args = parser.parse_args()
    with TemporaryDirectory() as tmp:
        check(args.binary.resolve(), Path(tmp))
