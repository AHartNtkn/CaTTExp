"""Compute the aligned cube retraction on full tableaux and its residual facet types."""
from argparse import ArgumentParser
from collections import Counter
from itertools import combinations, product
from pathlib import Path

from canonical_gray_cube import build_cube
from catt import STAR, arr, fv_tm, infer, subst_ty, tdim, v
from ct_suspension import ident
from emit_agda import Emitter
from rc2 import kappa, rc2

from relative_coherence_cube_boundary import boundary
from relative_coherence_omission_carriers import instruction
from relative_coherence_oriental_wedges import simplex_atom, simplex_d
from relative_coherence_steiner_cuts import tableau


def retained(face):
    stop = face.index(-1) if -1 in face else len(face)
    return tuple(i for i in range(stop) if face[i] == 0) + (stop,)


def basis(face):
    simplex = retained(face)
    return (simplex,) if len(simplex) == face.count(0) + 1 else ()


def chart(face):
    simplex = retained(face)
    dead = tuple(i for i in reversed(range(simplex[-1] + 1, len(face))) if face[i] == 0)
    return dead, simplex


def restrict_chart(face, subface):
    """Restrict successive last-coordinate deletions, then the intrinsic fold."""
    dead, simplex = chart(face)
    deleted = tuple(i for i in dead if subface[i] == 0)
    kept_axes = simplex[:-1]
    local_dead, local_simplex = chart(tuple(subface[i] for i in kept_axes))
    return deleted + tuple(kept_axes[i] for i in local_dead), tuple(simplex[i] for i in local_simplex)


def check_rank(n):
    faces = product((-1, 0, 1), repeat=n)
    facets = Counter()
    stationary = []
    for face in faces:
        simplex = retained(face)
        degree = face.count(0)
        change = Counter()
        for f, coefficient in boundary(face):
            change.update({cell: coefficient for cell in basis(f)})
            assert restrict_chart(face, f) == chart(f)
        wanted = simplex_d(simplex) if degree and basis(face) else Counter()
        assert change == wanted
        rows = tuple(tuple(tuple(sorted(s for f in side for s in basis(f))) for side in row)
                     for row in tableau(face))
        identities = degree + 1 - len(simplex)
        assert rows == simplex_atom(simplex) + (((), ()),) * identities
        if degree == n - 1:
            if identities:
                stationary.append(simplex)
            else:
                facets[simplex] += 1
    assert facets == Counter(combinations(range(n + 1), n))
    assert sorted(stationary, key=len) == [tuple(range(j)) for j in range(1, n)]
    for size in range(1, n + 2):
        for simplex in combinations(range(n + 1), size):
            # instruction uses 0,1,2 for fixed zero, fixed one, and free.
            image = [s for tile in instruction(n, simplex)
                     for s in basis(tuple((-1, 1, 0)[x] for x in tile))]
            assert image == [simplex]
    print(f'{n}-cube: {3**n} whole tableaux, {2**(n+1)-1} section instructions, '
          f'{len(facets)} different nondegenerate facets, {len(stationary)} stationary.')


def six_slices():
    for d in (2, 3, 4):
        simplex = tuple(range(d+1))
        rows = simplex_atom(simplex)
        if d < 4:
            slices = [rows + (((), ()),) * (3-d)]
        else:
            neg, pos = rows[3]
            slices = [rows[:3] + ((side, side),) for side in (neg, pos)]
        print(f'Stationary facet over O{d}: cut-three joins '
              f'{[q[3][0] for q in slices]}')
        if d == 4:
            assert [len(q[3][0]) for q in slices] == [2, 3]
    cubical_joins = tableau((0,)*4)[3]
    assert [len(s) for s in cubical_joins] == [4, 4]
    print('The last-coordinate deletion has two cut-three joins:', cubical_joins)


def raw_deletion(output):
    cube, _ = build_cube()
    # Use the last-negative square in the original ambient context. Every image
    # is built solely from that dependency-closed face.
    images = []
    square = next(i for i, ty in enumerate(cube) if tdim(ty) == 1)
    carried = fv_tm(cube[square][2]) | fv_tm(cube[square][3]) | {square}
    emitter = Emitter()
    for i, ty in enumerate(cube):
        required = subst_ty(ty, images)
        if ty == STAR:
            term = v(i % 4)
        else:
            a, b = required[2:]
            if tdim(ty) == 0:
                term = ident(cube, a) if a == b else v(cube.index(required))
            elif tdim(ty) == 1:
                term = v(square) if required == cube[square] else kappa(cube, a, b)
            else:
                term = rc2(cube, a, b)
                reverse = rc2(cube, b, a)
                reverse_type = arr(infer(cube, b), b, a)
                assert infer(cube, reverse) == reverse_type
                assert fv_tm(reverse) <= carried
                if output:
                    emitter.check_type('reverse', cube, reverse, reverse_type)
        assert infer(cube, term) == required
        assert fv_tm(term) <= carried
        images.append(term)
        if output:
            emitter.check_type('delete'+str(i), cube, term, required)
    if output:
        output.write_text(emitter.module(output.stem, 'Deletion of the last cube coordinate.'))
    print('Checked 27 raw entries for the three-cube deletion and its reversed top comparison.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--cube', type=int, default=7)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    for n in range(1, args.cube+1):
        check_rank(n)
    six_slices()
    raw_deletion(args.agda)
