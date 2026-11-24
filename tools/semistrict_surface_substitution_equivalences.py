"""Recognize strict generator bijections of typed raw ordinary substitutions."""
import argparse
from dataclasses import dataclass
from functools import cache
from itertools import zip_longest
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, chain_tree, check_ctx, comp2, disc_tree, glue_tree, infer,
                  maximal_vars, ps_dim, src, subst_ty, tdim_tm, tgt, tree_ctx, tree_of,
                  ucomp, v)
from ct_suspension import ident
from partial_cylinder_steiner import trees
from rc_oracle import strict_image
from semistrict_surface_exact_boundary import accepted, run
from semistrict_surface_computad_folds import disc_head
from steiner import Complex, image_to_cell


@dataclass(frozen=True)
class Shadow:
    # Row r records a positive generator count on the iterated r-source.
    rows: tuple
    generator: int | None


def compose(cut, left, right):
    pairs = zip_longest(left.rows, right.rows, fillvalue=False)
    rows = tuple(a if r <= cut else a or b for r, (a, b) in enumerate(pairs))
    for active, partner in ((left, right), (right, left)):
        if len(active.rows) == len(rows) and not any(partner.rows[cut+1:]):
            return Shadow(rows, active.generator)
    return Shadow(rows, None)


@cache
def shadow(ctx, term):
    rank = tdim_tm(ctx, term)
    if term[0] == 'v':
        lower = shadow(ctx, src(ctx, term)).rows if rank else ()
        return Shadow(lower + (rank > 0,), term[1])
    _, arity, _, labels = term
    if rank > ps_dim(arity):
        return Shadow(shadow(ctx, src(ctx, term)).rows + (False,), None)

    # Read child target and arrow slots in the declaration order of tree_ctx.
    next_slot = iter(range(1, len(arity)))

    def total(node, pole, depth):
        if not node:
            return shadow(ctx, labels[pole])
        value = None
        for child in node:
            next(next_slot)
            piece = total(child, next(next_slot), depth + 1)
            value = piece if value is None else compose(depth, value, piece)
        return value

    return total(tree_of(arity), 0, 0)


def recognizes_equivalence(domain, codomain, images):
    check_ctx(domain)
    check_ctx(codomain)
    if len(images) != len(domain):
        raise ValueError('one raw image per declaration is required')
    generators = []
    for ty, term in zip(domain, images):
        if infer(codomain, term) != subst_ty(ty, images):
            raise ValueError('substitution image has the wrong raw boundary')
        generators.append(shadow(codomain, term).generator)
    return len(generators) == len(codomain) and set(generators) == set(range(len(codomain)))


def pad(ctx, term, rank):
    for _ in range(rank - tdim_tm(ctx, term)):
        term = ident(ctx, term)
    return term


def check_terms():
    units = whiskers = 0
    for n in range(1, 6):
        ctx = tree_ctx(disc_tree(n))
        var = v(len(ctx)-1)
        for j in range(n):
            for left in (False, True):
                face = var
                for _ in range(n-j):
                    face = (src if left else tgt)(ctx, face)
                for p in range(j+1, n+1):
                    side = pad(ctx, face, p)
                    args = (side, var) if left else (var, side)
                    word = comp2(ctx, j, *args)
                    assert shadow(ctx, disc_head(ctx, word)).generator == var[1]
                    units += 1
                for k in range(j+1, n+1):
                    ranks = (k, n) if left else (n, k)
                    paste = tree_ctx(glue_tree(ranks[0], j, ranks[1]))
                    a, b = map(v, maximal_vars(paste))
                    side, active = (a, b) if left else (b, a)
                    for p in range(k, n+1):
                        partner = pad(paste, side, p)
                        args = (partner, active) if left else (active, partner)
                        assert shadow(paste, comp2(paste, j, *args)).generator is None
                        whiskers += 1
    chain = tree_ctx(chain_tree(3))
    assert shadow(chain, ucomp(chain)).generator is None
    parallel = (STAR, STAR, arr(STAR, v(0), v(1)), arr(STAR, v(0), v(1)))
    labels = (v(0), v(1), v(3), disc_head(parallel, v(2)))
    assert recognizes_equivalence(parallel, parallel, labels)
    assert not recognizes_equivalence(parallel, parallel, (*labels[:3], labels[2]))
    print(f'Checked {units} unit cuts, {whiskers} nonunit cuts, and typed substitution controls.')


def check_tableaux():
    checked = 0
    for size in range(6):
        for tree in trees(size):
            ctx = tree_ctx(tree)
            complex_ = Complex(ctx)
            atoms = {complex_.atom(i): i for i in range(len(ctx))}
            total = ucomp(ctx)
            terms = [total, ident(ctx, total), *(v(i) for i in range(len(ctx)))]
            if size:
                terms.append(disc_head(ctx, total))
            for term in terms:
                tableau = image_to_cell(strict_image(ctx, term))
                rows = (False,) + tuple(bool(minus) for minus, _ in tableau[1:])
                assert shadow(ctx, term) == Shadow(rows, atoms.get(tableau))
                checked += 1
    print(f'Compared {checked} shadows with full Steiner tableaux on globular trees.')


def winding(k, base):
    for _ in range(k):
        base = f'comp[eh(x,a,a),{base}]'
    return base


def check_rice(checkout, bound):
    scalar = '(x : *) (a : id(x) -> id(x))'
    variable = '(p : comp[a,a] -> comp[a,a])'
    identity = 'id(comp[a,a])'
    lines = ['import examples/eh']
    names = []
    for total in range(bound+1):
        endpoint = winding(total, identity)
        for m in range(total+1):
            source = winding(m, 'p')
            name = f'marked_{total}_{m}'
            lines.append(f'def {name} {scalar} {variable} (q : {source} -> {endpoint}) : '
                         f'{source} -> {endpoint} = q')
            names.append(name)
            name = f'specialize_{total}_{m}'
            p_label = winding(total-m, identity)
            lines.append(f'def {name} {scalar} : {endpoint} -> {endpoint} = '
                         f'{names[-1]}(x,a,{p_label},id({endpoint}))')
            names.append(name)
    filename = 'Marked.catt'
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as folder:
        directory = Path(folder)
        (directory / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        (directory / filename).write_text('\n'.join(lines) + '\n')
        accepted(run(binary, directory, filename), filename, names)
    print(f'Rice checked {len(names)} exact raw marked boundaries and specializations.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rice-checkout', type=Path)
    parser.add_argument('--bound', type=int, default=4)
    args = parser.parse_args()
    check_terms()
    check_tableaux()
    if args.rice_checkout:
        check_rice(args.rice_checkout.resolve(), args.bound)
