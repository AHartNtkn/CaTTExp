"""Check the typing and cellular contraction formula of the left point join."""
from collections import Counter

from catt import STAR, arr, check_ctx, comp2, infer, tdim, tree_ctx, v
from partial_cylinder_steiner import trees
from relative_coherence_based_columns import difference


def point_join(base):
    ctx = base + (STAR,)
    apex = v(len(base))
    cone = []
    for i, ty in enumerate(base):
        original = v(i)
        if ty == STAR:
            source, target = apex, original
        else:
            faces = []
            lower = ty
            while lower != STAR:
                faces.append(lower[2][1])
                lower = lower[1]
            target = original
            for cut, face in enumerate(reversed(faces)):
                target = comp2(ctx, cut, cone[face], target)
            source = cone[ty[3][1]]
            assert infer(ctx, target) == infer(ctx, source)
        for_old = v(len(ctx))
        ctx += (arr(infer(ctx, source), source, target),)
        cone.append(for_old)
        boundary = Counter({i: 1})
        if ty == STAR:
            boundary[apex[1]] -= 1
        else:
            boundary[cone[ty[2][1]][1]] += 1
            boundary[cone[ty[3][1]][1]] -= 1
            assert source[0] == 'v'
        assert difference(ctx, source, target) == {j: n for j, n in boundary.items() if n}
    check_ctx(ctx)
    return ctx, cone


def verify():
    arities = cells = 0
    dimensions = Counter()
    for edges in range(7):
        for tree in trees(edges):
            base = tree_ctx(tree)
            if max(tdim(ty) + 1 for ty in base) > 4:
                continue
            ctx, cone = point_join(base)
            for term in cone:
                dimensions[tdim(infer(ctx, term)) + 1] += 1
            arities += 1
            cells += len(base)
    print(f'{arities} globular arities; {cells} checked cone variables by rank:', dict(sorted(dimensions.items())))


if __name__ == '__main__':
    verify()
