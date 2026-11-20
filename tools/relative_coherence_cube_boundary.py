"""Integral facet incidence and a literal CaTT instance of the boundary test in R6."""
from argparse import ArgumentParser
from collections import Counter, defaultdict, deque
from itertools import combinations, product
from pathlib import Path

from canonical_gray_cube import build_cube, mask, square_chain
from catt import STAR, arr, check_ctx, infer, subst_ty, v
from emit_agda import Emitter


def boundary(face):
    """Coordinate 0 is free; the orientation uses free axes in increasing order."""
    sign = 1
    for axis, entry in enumerate(face):
        if entry == 0:
            for side in (-1, 1):
                yield face[:axis] + (side,) + face[axis + 1:], sign * side
            sign = -sign


def check_cube_boundary(dimension):
    faces = set(product((-1, 0, 1), repeat=dimension))
    top = (0,) * dimension
    facets = dict(boundary(top))
    ridge_equations = defaultdict(list)
    for face in faces:
        twice = Counter()
        for child, sign in boundary(face):
            assert child in faces
            for ridge, orientation in boundary(child):
                twice[ridge] += sign * orientation
                if face == top:
                    ridge_equations[ridge].append((child, orientation))
        assert not any(twice.values())

    # Solve all integral top-cycle equations, normalizing one coefficient to 1.
    adjacent = defaultdict(list)
    for incident in ridge_equations.values():
        (left, a), (right, b) = incident
        adjacent[left].append((right, -a * b))
        adjacent[right].append((left, -a * b))
    first = next(face for face in facets if facets[face] == 1)
    coefficients = {first: 1}
    queue = deque([first])
    while queue:
        face = queue.popleft()
        for other, ratio in adjacent[face]:
            expected = coefficients[face] * ratio
            if other in coefficients:
                assert coefficients[other] == expected
            else:
                coefficients[other] = expected
                queue.append(other)
    assert coefficients == facets
    print(f"{len(faces) - 1} proper faces, {len(coefficients)} facets, "
          f"{len(ridge_equations)} ridge equations, primitive integral top cycle")


def check_three_cube(agda_path):
    cube, _ = build_cube()
    # A finite part of P(V): include all ordered vertex pairs first, so that
    # the actual inclusion of the cube changes the levels in its attaching terms.
    ambient = (STAR,) * 8
    generated = {}

    def on_boundary(ty):
        nonlocal ambient
        if ty not in generated:
            generated[ty] = v(len(ambient))
            ambient += (ty,)
        return generated[ty]

    for source, target in product(range(8), repeat=2):
        on_boundary(arr(STAR, v(source), v(target)))
    images = [v(i) for i in range(8)]
    for ty in cube[8:]:
        images.append(on_boundary(subst_ty(ty, tuple(images))))
    assert len(set(images)) == len(cube)
    check_ctx(ambient)
    top = images[-1]
    ty = infer(ambient, top)
    actual = square_chain(ty[3])
    actual.subtract(square_chain(ty[2]))

    # Name facets from the cube generator order, independently of the two
    # hemisphere expressions whose occurrences were just counted.
    canonical = {}
    squares = iter(images[20:26])
    for vertex in range(8):
        for axes in combinations(range(3), 2):
            if not vertex & mask(axes):
                face = tuple(0 if i in axes else (1 if vertex & (1 << i) else -1)
                             for i in range(3))
                canonical[face] = next(squares)
    assert actual == Counter({canonical[face]: sign for face, sign in boundary((0, 0, 0))})
    assert len(ambient) == 79
    print("three-cube: 27 embedded generators; the literal top boundary has all six signed facets")
    if agda_path:
        emitter = Emitter()
        emitter.check_type("top", ambient, top, subst_ty(cube[-1], tuple(images[:-1])))
        agda_path.write_text(emitter.module(agda_path.stem, "Universal boundary, three-cube instance."))


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path, help="write the three-cube judgment to this .agda file")
    args = parser.parse_args()
    check_cube_boundary(6)
    check_three_cube(args.agda)
