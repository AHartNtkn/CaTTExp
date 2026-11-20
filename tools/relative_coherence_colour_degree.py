"""Find a relative cellular cycle of nonzero simplex degree in a typed CaTT context."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import lcm
from pathlib import Path

from canonical_gray_cube import build_cube
from catt import STAR, arr, check_ctx, fv_ty, infer, tdim, v
from relative_coherence_cut import top_counts


def add_scaled(target, source, factor):
    for index, coefficient in source.items():
        value = target.get(index, 0) + factor * coefficient
        if value:
            target[index] = value
        else:
            target.pop(index, None)


def cone(vertex, chain):
    result = {}
    for simplex, coefficient in chain.items():
        if vertex not in simplex:
            sign = (-1) ** sum(i < vertex for i in simplex)
            key = tuple(sorted((vertex, *simplex)))
            add_scaled(result, {key: coefficient}, sign)
    return result


def simplex_boundary(chain):
    result = {}
    for simplex, coefficient in chain.items():
        for i in range(len(simplex)):
            face = simplex[:i] + simplex[i + 1:]
            add_scaled(result, {face: coefficient}, (-1) ** i)
    return result


def degree_test(ctx, colours, degree):
    """Return (integer coefficients on context indices, signed degree), or None."""
    check_ctx(ctx)
    simplex = tuple(range(degree + 1))
    if degree < 1 or len(colours) != ctx.count(STAR) or not set(colours) <= set(simplex):
        raise ValueError("give one colour in 0..degree for every object")
    vertices = iter(colours)
    support, image, columns, volume = [], [], {}, {}
    for i, ty in enumerate(ctx):
        if ty == STAR:
            colour = next(vertices)
            support.append({colour})
            image.append({(colour,): 1})
            continue
        names = set().union(*(support[j] for j in fv_ty(ty)))
        support.append(names)
        boundary = dict(top_counts(ctx, ty[3]))
        add_scaled(boundary, top_counts(ctx, ty[2]), -1)
        faces = {}
        for j, multiplicity in boundary.items():
            add_scaled(faces, image[j], multiplicity)
        image.append(cone(min(names), faces))
        assert simplex_boundary(image[i]) == faces
        if tdim(ty) + 1 == degree:
            columns[i] = {j: a for j, a in boundary.items() if len(support[j]) == degree + 1}
            volume[i] = image[i].get(simplex, 0)

    # Keep each column operation on the generators as well as on the boundary.
    pivots = {}
    for i, column in columns.items():
        residual, combination = dict(column), {i: 1}
        while residual:
            j = min(residual)
            if j not in pivots:
                pivots[j] = residual, combination
                break
            pivot, old = pivots[j]
            factor = -Fraction(residual[j], pivot[j])
            add_scaled(residual, pivot, factor)
            add_scaled(combination, old, factor)
        if residual or not sum(a * volume[t] for t, a in combination.items()):
            continue
        denominator = lcm(*(Fraction(a).denominator for a in combination.values()))
        witness = {t: int(a * denominator) for t, a in combination.items()}
        check = {}
        for t, a in witness.items():
            add_scaled(check, columns[t], a)
        assert not check
        return witness, sum(a * volume[t] for t, a in witness.items())
    return None


def check_examples():
    cube, _ = build_cube()
    colours = [min([3] + [i for i in range(3) if mask >> i & 1]) for mask in range(8)]
    direct = degree_test(cube, colours, 3)
    assert direct is not None and abs(direct[1]) == 1
    # Subdivide the top globe by a 2-generator on its common 1-boundaries.
    base = cube[:-1]
    u, w = cube[-1][2:]
    mid = v(len(base))
    mid_type = infer(base, u)
    assert mid_type == infer(base, w)
    first = (*base, mid_type, arr(mid_type, u, mid))
    second = (*base, mid_type, arr(mid_type, mid, w))
    split = (*first, second[-1])
    assert degree_test(first, colours, 3) is None
    assert degree_test(second, colours, 3) is None
    combined = degree_test(split, colours, 3)
    assert combined is not None and abs(combined[1]) == 1
    assert combined[0] == {len(split) - 2: 1, len(split) - 1: 1}
    assert degree_test(split, [0] * 8, 3) is None
    totals = Counter()
    for tail in product(range(4), repeat=7):
        names = (0, *tail)
        # First occurrences in standard order give one representative per partition.
        if 3 not in names or any(x > 1 + max(names[:i]) for i, x in enumerate(tail, 1)):
            continue
        result = degree_test(cube, names, 3)
        totals[abs(result[1]) if result else 0] += 1
    assert totals == {0: 1527, 1: 174}
    print("All 1,701 surjective colourings up to permutation: 174 have absolute degree one.")
    print(f"Typed three-cube: {direct}. Split cube: {combined}. "
          "Both single halves and the constant colouring have zero relative degree.")


def immutable(value):
    return tuple(map(immutable, value)) if isinstance(value, list) else value


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, help="JSON with context, colours and degree")
    args = parser.parse_args()
    if args.input is None:
        check_examples()
    else:
        data = json.loads(args.input.read_text())
        print(degree_test(immutable(data["context"]), data["colours"], data["degree"]))
