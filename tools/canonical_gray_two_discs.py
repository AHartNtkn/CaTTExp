"""Construct and check CT for D² ⊗ D² by suspending the three-cube section."""
from functools import cache
from itertools import combinations, product
from pathlib import Path
import argparse

from canonical_gray_cube import build_cube
from catt import (STAR, arr, check_ctx, fv_ty, glue_tree, infer, maximal_vars,
                  ps_dim, sub_from, subst_tm, subst_ty, tdim, tree_ctx, v)
from ct_suspension import ident, susp_tm, susp_ty
from emit_agda import Emitter
from gray_globe_comparison import (atom, face, globe, image, strict_cells,
                                   suspend, verify)


def strict_interpreter(context, generators):
    """Evaluate the whole tableau, including lower whiskers and identities."""
    return tableau_interpreter(context, lambda index: atom(generators[index]))


def tableau_interpreter(context, variable_value):
    """Evaluate raw syntax with a specified strict tableau for each variable."""
    @cache
    def evaluate(term):
        if term[0] == 'v':
            return variable_value(term[1])
        _, arity, generic_type, args = term
        degree = tdim(generic_type) + 1
        # A strict composite uses all generators of its arity in top degree
        # once. A higher coherence has an empty top chain.
        assert degree >= ps_dim(arity)
        chain = tuple(sorted(g for ty, arg in zip(arity, args)
                             if tdim(ty) + 1 == degree
                             for g in evaluate(arg)[-1][0]))
        _, _, source, target = infer(context, term)
        left, right = evaluate(source), evaluate(target)
        assert left[:-1] == right[:-1]
        return left[:-1] + ((left[-1][0], right[-1][0]), (chain, chain))
    return evaluate


def cube_generators():
    for degree in range(4):
        for vertex in range(8):
            for moving in combinations(range(3), degree):
                if any(vertex & (1 << a) for a in moving):
                    continue
                yield tuple((1, 2) if a in moving else (0, (vertex >> a) & 1)
                            for a in range(3))


def check(emitter=None):
    lifts = verify(2, 2)
    cube, checks = build_cube()
    labels = list(cube_generators())
    cube_value = strict_interpreter(cube, labels)
    cube_terms = {cube_value(term): term for _, term, _ in checks}
    cube_terms.update((cube_value(v(i)), v(i)) for i in range(8))

    @cache
    def cube_term(cell):
        if cell in cube_terms:
            return cube_terms[cell]
        assert cell[-1] == ((), ())
        return ident(cube, cube_term(face(cell, 0)))

    indices = {}
    context = ()
    def declare(g, ty):
        nonlocal context
        indices[g] = len(context)
        context += (ty,)
        return v(indices[g])

    disc = globe(2)
    for g in sorted(product(disc, repeat=2), key=lambda pair: sum(d for d, _ in pair)):
        if all(d for d, _ in g):
            continue
        if any(d for d, _ in g):
            endpoints = [v(indices[face(atom(g), side)[-1][0][0]]) for side in (0, 1)]
            ty = arr(infer(context, endpoints[0]), *endpoints)
        else:
            ty = STAR
        declare(g, ty)

    def vertex(k):
        return v(indices[((0, k), (0, k))])

    rho = [vertex(0), vertex(1)]
    for g, ty in zip(labels, cube):
        prescribed = subst_ty(susp_ty(ty), rho)
        p, middle, q = g
        if middle[0]:
            term = declare((suspend(p), suspend(q)), prescribed)
        else:
            side = middle[1]
            # Restrict to the two globes used by this endpoint-panel atom.
            pieces = [(suspend(p), (0, 1 - side)), ((0, side), suspend(q))]
            if side == 0:
                pieces.reverse()
            dims = [sum(d for d, _ in piece) for piece in pieces]
            arity = tree_ctx(glue_tree(dims[0], 0, dims[1]))
            inc = sub_from(arity, context, dict(zip(maximal_vars(arity),
                                                    (v(indices[piece]) for piece in pieces))))
            rename = {arg[1]: v(i) for i, arg in enumerate(inc)}
            assert fv_ty(prescribed) <= rename.keys() and len(rename) == len(inc)
            term = ('coh', arity, subst_ty(prescribed, rename), inc)
        assert infer(context, term) == prescribed
        rho.append(term)

    check_ctx(context)
    assert len(indices) == len(context) == 25
    value = strict_interpreter(context, tuple(indices))
    for i, g in enumerate(labels):
        assert value(rho[i + 2]) == image(atom(g))

    terms = {atom(g): v(i) for g, i in indices.items()}
    for degree in range(5):
        cells = strict_cells((2, 2), degree)
        for i, cell in enumerate(sorted(cells)):
            if cell in lifts:
                term = subst_tm(susp_tm(cube_term(lifts[cell])), rho)
            elif cell in terms:
                term = terms[cell]
            else:
                assert cell[-1] == ((), ())
                term = ident(context, terms[face(cell, 0)])
            if cell in terms:
                assert term == terms[cell]  # pins every generator
            expected = STAR
            if degree:
                left, right = [terms[face(cell, d)] for d in (0, 1)]
                expected = arr(infer(context, left), left, right)
            assert infer(context, term) == expected
            assert value(term) == cell
            terms[cell] = term
            if emitter is not None and cell[-1][0]:
                emitter.check_type(f'cell-{degree}-{i}', context, term, expected)
        print(f'D² ⊗ D², degree {degree}: {len(cells)} terms checked')
    return terms


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--emit', action='store_true', help='regenerate the Agda type checks')
    args = parser.parse_args()
    emitter = Emitter() if args.emit else None
    check(emitter)
    if args.emit:
        target = Path(__file__).resolve().parents[1] / 'src/CaTTExp/Generated/CanonicalGrayTwoDiscs.agda'
        target.write_text(emitter.module('CaTTExp.Generated.CanonicalGrayTwoDiscs',
                                         'From tools/canonical_gray_two_discs.py.'))
