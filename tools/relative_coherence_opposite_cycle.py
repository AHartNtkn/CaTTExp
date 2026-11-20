"""Repair a degree-zero opposite-face boundary using only proper raw brackets."""
from functools import cache

from canonical_gray_cube import build_cube
from catt import STAR, check_ctx, comp2, tdim, v
from relative_coherence_based_columns import Brackets
from relative_coherence_colour_degree import add_scaled, simplex_boundary
from relative_coherence_face_transfer import Transfer, lift, reduced
from relative_coherence_path_cones import replace
from relative_coherence_polarized_cube import check as check_cube


def linear(vector, transform):
    total = {}
    for i, coefficient in vector.items():
        add_scaled(total, transform(i), coefficient)
    return total


class Repair(Transfer):
    def contract(self, q, chain):
        def step(i):
            ty = self.ctx[i]
            if ty == STAR:
                return {self.p.bracket(v(q), v(i))[1]: 1}
            if tdim(ty) == 0:
                x, y = ty[2:]
                qx, qy = self.p.bracket(v(q), x), self.p.bracket(v(q), y)
                triangle = self.p.bracket(comp2(self.ctx, 0, qx, v(i)), qy)
                return {triangle[1]: -1}
            assert tdim(ty) == 1
            return {replace(self.p, q, v(i))[1]: 1}
        return linear(chain, step)

    @cache
    def section(self, face):
        if len(face) == 1:
            return {face[0]: 1}
        boundary = linear(simplex_boundary({face: 1}), self.section)
        return self.contract(min(face), boundary)

    @cache
    def homotopy(self, i):
        residue = {i: 1}
        add_scaled(residue, linear(self.image(i), self.section), -1)
        if self.ctx[i] != STAR:
            add_scaled(residue, linear(self.boundary({i: 1}, 0), self.homotopy), -1)
        filler = self.contract(min(self.names(i)), residue)
        assert self.boundary(filler, 0) == residue
        assert all(self.names(j) <= self.names(i) for j in filler)
        return filler


def verify():
    p = Brackets(5)
    solver = Repair(p, 4)
    cube, _ = build_cube()
    colours = [1 + min([3] + [i for i in range(3) if mask >> i & 1]) for mask in range(8)]
    g = lift(cube, colours, p)[-1][1]
    other = solver.relabel(g, (0, 2, 3, 1, 4))[1]
    assert abs(solver.image(g)[(1, 2, 3, 4)]) == 1 and solver.image(other) == solver.image(g)
    signed = {other: 1, g: -1}
    boundary = solver.boundary(signed, 0)
    assert boundary and not linear(boundary, solver.image)
    assert all(len(solver.names(i)) < 4 for i in boundary)
    repair = linear(boundary, solver.homotopy)
    assert solver.boundary(repair, 0) == boundary
    assert all(len(solver.names(i)) < 4 for i in repair)
    absolute = signed.copy()
    add_scaled(absolute, repair, -1)
    assert not solver.boundary(absolute, 0)
    for modulus in (0, 2, 4, 5):
        lhs = solver.project({other: 1}, 0, range(1, 5), modulus)
        rhs = solver.project({g: 1}, 0, range(1, 5), modulus)
        add_scaled(rhs, solver.project(absolute, 0, range(1, 5), modulus), 1)
        assert reduced(rhs, modulus) == lhs
    check_ctx(p.ctx)
    print(f'{len(boundary)} boundary coordinates, {len(repair)} proper repair coordinates, '
          f'{len(absolute)} absolute-cycle coordinates. Polarizations agree integrally and modulo 2, 4, 5.')
    check_cube(6)


if __name__ == '__main__':
    verify()
