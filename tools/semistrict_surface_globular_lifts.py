"""Exercise positional lifting of binary equations and attachments above suspended scalars."""
import argparse
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, check_ctx, comp2, glue_tree, infer, maximal_vars, sub_from,
                  subst_tm, subst_ty, tree_ctx, v)
from ct_suspension import susp_ctx
from emit_agda import Emitter
from rc_oracle import _top, vfactors
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_scalar_cube import exchange
from semistrict_surface_skeletal_base import right_unit


def loop_context(rank, names):
    ctx = [STAR]
    for i in range(rank):
        ty = arr(ctx[i], v(i), v(i))
        ctx.extend([ty] * (names if i + 1 == rank else 1))
    return tuple(ctx)


def word(ctx, rank, letters):
    if not letters:
        return identity(ctx, v(rank - 1))
    answer = v(rank + letters[0])
    for letter in letters[1:]:
        answer = comp2(ctx, rank - 1, answer, v(rank + letter))
    return answer


def read_word(ctx, rank, term):
    letters = []
    for factor in vfactors(ctx, term, rank):
        if factor[0] == 'v':
            letters.append(factor[1] - rank)
        else:
            assert factor == identity(ctx, v(rank - 1))
    return tuple(letters)


def associators(ctx, cut, terms):
    a, b, c = terms
    return (comp2(ctx, cut, comp2(ctx, cut, a, b), c),
            comp2(ctx, cut, a, comp2(ctx, cut, b, c)))


def check_lifts(emitter):
    tested = 0
    for rank in range(1, 5):
        shape = tree_ctx(string_tree(rank - 1, [rank] * 3))
        ambient = tree_ctx(string_tree(rank - 1, [rank] * 4))
        slots = maximal_vars(shape)
        bigger_slots = maximal_vars(ambient)
        assert ambient[:len(shape)] == shape
        sides = associators(shape, rank - 1, list(map(v, slots)))
        clauses = (*sides, head(shape, *sides), head(shape, *reversed(sides)),
                   identity(shape, sides[0]), identity(shape, sides[1]))
        # Fold two upstairs colours to 0. The last downstairs generator, 1,
        # is outside the image, including the image of all strict pastes.
        up = loop_context(rank, 2)
        down = loop_context(rank, 2)
        fold = tuple(map(v, range(rank))) + (v(rank), v(rank))
        for lengths in product(range(3), repeat=3):
            grey = [word(down, rank, (0,) * length) for length in lengths]
            inputs = dict(zip(bigger_slots, [*grey, v(rank + 1)]))
            sigma = sub_from(ambient, down, inputs)
            assert all(infer(down, x) == subst_ty(ty, sigma) for x, ty in zip(sigma, ambient))
            seen = set()
            # Enumerate lifts independently at each slot, then recover the
            # slot labels from only the final coloured paste and its cuts.
            choices = [list(product(range(2), repeat=n)) for n in lengths]
            for pieces in product(*choices):
                paste = sum(pieces, ())
                assert paste not in seen
                seen.add(paste)
                cuts = (0, lengths[0], sum(lengths[:2]), len(paste))
                labels = [word(up, rank, paste[i:j]) for i, j in zip(cuts, cuts[1:])]
                tau = sub_from(shape, up, dict(zip(slots, labels)))
                for i, term in enumerate(clauses):
                    lifted = subst_tm(term, tau)
                    target = subst_tm(term, sigma)
                    if i < 2:
                        assert read_word(up, rank, lifted) == paste
                    assert subst_tm(lifted, fold) == target
                    assert infer(up, lifted) == subst_ty(infer(shape, term), tau)
                    if pieces == ((0, 1), (), (1,)):
                        emitter.check_type(f'lift{rank}term{i}', up, lifted, infer(up, lifted))
                        emitter.check_eq(f'fold{rank}term{i}', lifted, fold, target)
                tested += 1
            assert seen == set(product(range(2), repeat=sum(lengths)))
    print(f'Checked {tested} positional lifts of both word sides, both coherence orientations and their identities.')


def read_square_face(ctx, face):
    columns = [None, None]
    for whisker in vfactors(ctx, face, 2):
        arity, labels = whisker[1], whisker[3]
        slots = maximal_vars(arity)
        if arity == tree_ctx(glue_tree(2, 0, 1)):
            column = 0
        else:
            assert arity == tree_ctx(glue_tree(1, 0, 2))
            column = 1
        assert columns[column] is None
        columns[column] = read_word(ctx, 2, labels[slots[column]])
    return tuple(columns)


def check_square(emitter):
    ctx = loop_context(2, 2)
    fold = (v(0), v(1), v(2), v(2))
    pair = tree_ctx(glue_tree(2, 0, 2))
    generic = exchange(pair, *map(v, maximal_vars(pair)))
    options = [letters for n in range(3) for letters in product(range(2), repeat=n)]
    for left, right in product(options, repeat=2):
        a, b = word(ctx, 2, left), word(ctx, 2, right)
        lifted = exchange(ctx, a, b)
        downstairs = exchange(ctx, subst_tm(a, fold), subst_tm(b, fold))
        assert subst_tm(lifted, fold) == downstairs
        slots = maximal_vars(pair)
        tau = sub_from(pair, ctx, dict(zip(slots, (a, b))))
        assert infer(ctx, lifted) == subst_ty(infer(pair, generic), tau)
        for face in infer(ctx, lifted)[2:]:
            assert read_square_face(ctx, face) == (left, right)
        if left == (0, 1) and right == (1, 0):
            emitter.check_type('liftedSquare', ctx, lifted, infer(ctx, lifted))
            emitter.check_eq('foldedSquare', lifted, fold, downstairs)
            swapped = exchange(ctx, b, a)
            assert swapped != lifted and subst_tm(swapped, fold) == downstairs
            for face in infer(ctx, swapped)[2:]:
                assert read_square_face(ctx, face) == (right, left)
    print(f'Checked {len(options)**2} lifts of the directed square with two separately labelled event lists.')


def check_attachments(emitter):
    vertex = (STAR,)
    unit = identity(vertex, v(0))
    ctx = vertex + (arr(infer(vertex, unit), unit, unit),)
    for shift in range(1, 4):
        ctx = susp_ctx(ctx)
        rank = shift + 2
        scalar = v(len(ctx) - 1)
        # Make a fresh (rank+1)-cell at a composite of suspended scalars.
        # A second attachment departs from a different writing of that cell.
        seam = comp2(ctx, rank - 1, scalar, scalar)
        new_ty = arr(infer(ctx, seam), seam, seam)
        relative = ctx + (new_ty, new_ty)
        new, other = v(len(ctx)), v(len(ctx) + 1)
        correction = right_unit(relative, new, rank + 1, insert=True)
        assert infer(relative, correction)[2] == new
        padded = infer(relative, correction)[3]
        extended = relative + (arr(new_ty, padded, other),)
        check_ctx(extended)
        declaration = v(len(relative))
        fitted = comp2(extended, rank + 1, correction, declaration)
        expected = arr(new_ty, new, other)
        assert infer(extended, declaration) != expected
        assert infer(extended, fitted) == expected
        assert _top(extended, fitted) == {len(relative): 1}
        emitter.check_type(f'suspended{shift}fit', extended, fitted, expected)
    print('Checked fitted 5-, 6- and 7-cells over one, two and three suspensions of a scalar.')


def check_insertion(binary):
    surface = """def ass = coh [ x{f}y{g}z{h}t : comp[comp[f,g],h] -> comp[f,comp[g,h]] ]
def back = coh [ x{f}y{g}z{h}t : comp[f,comp[g,h]] -> comp[comp[f,g],h] ]
def unused_edge (x : *) (f : x -> x) (z : x -> x) : comp[comp[f,f],f] -> comp[f,comp[f,f]] = id(comp[comp[f,f],f])
def lift_assoc (x : *) (p : x -> x) (q : x -> x) : ass(p,q,p) -> id(comp[p,comp[q,p]]) = id(ass(p,q,p))
def lift_back (x : *) (p : x -> x) (q : x -> x) : back(p,q,p) -> id(comp[comp[p,q],p]) = id(back(p,q,p))
def converted_slot (x : *) (p : x -> x) (q : x -> x) (a : comp[comp[p,q],p] -> p) (b : p -> comp[p,comp[q,p]]) : p -> p = comp[b,a]
"""
    wrong_order = """def incompatible (x : *) (p : x -> x) (q : x -> x) : comp[comp[p,q],p] -> comp[q,comp[p,p]] = id(comp[comp[p,q],p])
"""
    with TemporaryDirectory() as folder:
        directory = Path(folder)
        (directory / 'Folded.catt').write_text(surface)
        (directory / 'Reordered.catt').write_text(wrong_order)
        accepted(run(binary, directory, 'Folded.catt', ['--sua']), 'Folded.catt',
                 ['unused_edge', 'lift_assoc', 'lift_back', 'converted_slot'])
        rejected(run(binary, directory, 'Folded.catt'), 'Folded.catt', 'unused_edge')
        rejected(run(binary, directory, 'Reordered.catt', ['--sua']), 'Reordered.catt', 'incompatible')
    print('Insertion checked both lifted comparisons and the converted slot, and rejected the permuted boundary.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    parser.add_argument('--catt-strict', type=Path, help='also check the converted typings with Rice’s implementation')
    args = parser.parse_args()
    emitter = Emitter()
    check_lifts(emitter)
    check_square(emitter)
    check_attachments(emitter)
    if args.catt_strict:
        check_insertion(args.catt_strict.resolve())
    if args.agda_dir:
        for prefix, kernel in [('Ordinary', 'CaTTExp.Pure'), ('Gray', 'CaTTExp.Gray.Pure')]:
            name = prefix + 'GlobularSurfaceLifts'
            source = emitter.module(name, __doc__).replace('open import CaTTExp.Pure', 'open import ' + kernel)
            (args.agda_dir / (name + '.agda')).write_text(source)


if __name__ == '__main__':
    main()
