"""Lift full-colour hom-chain certificates at two fixed endpoints to absolute chains."""
from argparse import ArgumentParser
from itertools import combinations
from pathlib import Path

from catt import STAR, arr, comp2, disc_tree, fv_tm, infer, maximal_vars, sub_from, subst_tm, tdim, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_based_columns import Brackets
from relative_coherence_colour_degree import add_scaled, simplex_boundary
from relative_coherence_exchange_faces import head
from relative_coherence_face_transfer import Transfer, reduced
from relative_coherence_hom_chains import boundary, hom_chain

INSIDE = (2, 3, 4, 5)


def subsets():
    for size in range(len(INSIDE)+1):
        yield from combinations(INSIDE, size)


def rename_term(track, term, subset):
    names = tuple(0 if i in subset else i for i in range(7))
    if term[0] == 'v':
        return track.relabel(term[1], names)
    return (*term[:3], tuple(rename_term(track, t, subset) for t in term[3]))


def project(track, chain):
    result = {}
    for subset in subsets():
        for term, n in chain.items():
            value = rename_term(track, term, subset)
            add_scaled(result, {value: n}, (-1)**len(subset))
    return result


def differential(p, chain):
    result = {}
    for term, n in chain.items():
        add_scaled(result, boundary(p.ctx, term), n)
    return result


def lift_certificate(track, u, w, columns, *, multiple=1, modulus=0, emit=None):
    """Verify full rows, then return an absolute chain on the same multiple of the pair."""
    if modulus != 0 and modulus < 2:
        raise ValueError('modulus must be zero or at least two')
    p = track.p
    ty = infer(p.ctx, u)
    assert ty == infer(p.ctx, w) and tdim(ty) == 3
    while ty[1] != STAR:
        ty = ty[1]
    assert ty[2:] == (v(6), v(1))
    for term in (u, w, *columns):
        assert all(not set(range(1, 7)) <= track.names(i) for i in fv_tm(term))
    target = {}
    add_scaled(target, hom_chain(p.ctx, w), multiple)
    add_scaled(target, hom_chain(p.ctx, u), -multiple)
    for term in columns:
        cell_type = infer(p.ctx, term)
        assert tdim(cell_type) == 4 and hom_chain(p.ctx, term) == {term: 1}
        while cell_type[1] != STAR:
            cell_type = cell_type[1]
        assert cell_type == ty
    error = differential(p, columns)
    add_scaled(error, target, -1)
    full = {t: n for t, n in error.items() if set(INSIDE) <= track.support(t)}
    if reduced(full, modulus):
        raise ValueError('nonzero residual on full-colour rows')
    absolute = project(track, columns)
    for subset in subsets():
        if not subset:
            continue
        a, b = (rename_term(track, value, subset) for value in (u, w))
        correction = p.bracket(a, b)
        expected = arr(infer(p.ctx, a), a, b)
        assert infer(p.ctx, correction) == expected
        assert not track.support(correction).intersection(subset)
        add_scaled(absolute, {correction: 1}, multiple * (-1)**(len(subset)+1))
        if emit:
            emit(subset, correction, expected)
    assert reduced(differential(p, absolute), modulus) == reduced(target, modulus)
    return reduced(absolute, modulus)


def example(power, emitter):
    p = Brackets(7)
    track = Transfer(p, 6)
    prefix = p.bracket(v(6), v(5))
    for j in (5, 4, 3):
        edge = p.bracket(v(j), v(j-1))
        prefix = comp2(p.ctx, 0, prefix, edge)
    loop = p.bracket(v(2), v(2))
    for _ in range(power):
        prefix = comp2(p.ctx, 0, prefix, loop)
    last = p.bracket(v(2), v(1))
    globe = ident(p.ctx, ident(p.ctx, last))
    chart = tree_ctx(((),) + disc_tree(3))
    a, b = maximal_vars(chart)
    whiskered = comp2(chart, 0, v(a), v(b))
    nontrivial = head(chart, whiskered, whiskered)
    unit = ident(chart, whiskered)
    sigma = sub_from(chart, p.ctx, {a: prefix, b: globe})
    for reverse in (False, True):
        s, t = (unit, nontrivial) if reverse else (nontrivial, unit)
        u, w = subst_tm(s, sigma), subst_tm(t, sigma)
        filler = subst_tm(head(chart, s, t), sigma)
        expected = arr(infer(p.ctx, u), u, w)
        assert infer(p.ctx, filler) == expected
        target = boundary(p.ctx, filler)
        assert len(target) == 1
        assert all(track.support(term) == set(range(1, 7)) for term in target)
        column = hom_chain(p.ctx, filler)
        assert column == {filler: 1}
        # An input certificate can have arbitrary extra proper columns.
        noise = rename_term(track, filler, (2,))
        relative = dict(column)
        add_scaled(relative, {noise: 9}, 1)
        assert differential(p, relative) != target
        absolute = project(track, relative)
        polarized = project(track, target)
        assert len(polarized) == 16
        assert differential(p, absolute) == polarized
        def emit(subset, correction, ty):
            if emitter:
                name = ('back' if reverse else 'out') + ''.join(map(str, subset))
                emitter.check_type(name, p.ctx, correction, ty)
        lift_certificate(track, u, w, relative, emit=emit)
        modular = {filler: 7, noise: 9}
        lift_certificate(track, u, w, modular, multiple=2, modulus=5)
        try:
            lift_certificate(track, u, w, modular, multiple=2)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted a modular certificate over the integers')
        if emitter:
            emitter.check_type('chartBack' if reverse else 'chartOut', p.ctx, filler, expected)


def simplex_projection(chain):
    result = {}
    for subset in subsets():
        for simplex, n in chain.items():
            image = [0 if i in subset else i for i in simplex]
            if len(set(image)) != len(image):
                continue
            inversions = sum(a > b for i, a in enumerate(image) for b in image[i+1:])
            add_scaled(result, {tuple(sorted(image)): n}, (-1)**(len(subset)+inversions))
    return result


def facet_check():
    positive = tuple(range(1, 7))
    filling = {positive: 1}
    add_scaled(filling, simplex_boundary({(0, *positive): 1}), -1)
    exterior = simplex_projection(filling)
    assert exterior == {(0, 2, 3, 4, 5, 6): 1, (0, 1, 2, 3, 4, 5): -1}
    assert simplex_boundary(exterior) == simplex_projection(simplex_boundary({positive: 1}))
    for simplex in filling:
        residue = {face: n for face, n in simplex_boundary({simplex: 1}).items() if 0 not in face}
        assert len(residue) == 1  # a different unrooted boundary coordinate for each facet


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    facet_check()
    for power in (0, 1, 4):
        example(power, emitter if power == 0 else None)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Four-colour polarization and both corrected boundary directions.'))
    print('Six integral and six modular certificates lifted; six integral mismatches rejected. '
          '96 polarized target terms and 90 proper bracket orientations checked. '
          'Both forced six-name exterior facet coefficients checked.')
