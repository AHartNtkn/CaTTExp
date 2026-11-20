"""Verify the signed flag transfer and the two based cocycle identities."""
from collections import Counter
from itertools import combinations, permutations

from catt import arr, check_ctx, comp2, infer, v
from relative_coherence_based_columns import Brackets, difference
from relative_coherence_hidden_seam import identity


def flag_transfer(k):
    """Identify flags at all missing internal ranks and take the exterior quotient."""
    flags = []
    for order in permutations(range(k)):
        vertices = [0]
        for axis in order:
            vertices.append(vertices[-1] | (1 << axis))
        inversions = sum(a > b for a, b in combinations(order, 2))
        flags.append((tuple(vertices), (-1) ** inversions))
    assert len(set(path for path, _ in flags)) == len(flags)
    for mask in range(1 << (k + 1)):
        if mask & 1 and mask & (1 << k):
            image = Counter()
            for path, sign in flags:
                cell = tuple(x for i, x in enumerate(path) if mask & (1 << i))
                image[cell] += sign
            if mask == (1 << (k + 1)) - 1:
                assert len(image) == len(flags)
                assert image[tuple((1 << i) - 1 for i in range(k + 1))] == 1
            else:
                assert all(n == 0 for n in image.values())
        else:
            # Each flag lies in a cube boundary hyperplane on this whole subface.
            for path, _ in flags:
                vertices = [x for i, x in enumerate(path) if mask & (1 << i)]
                assert any(len({x >> j & 1 for x in vertices}) <= 1 for j in range(k))
    return len(flags)


def based_identities():
    p = Brackets(1)
    pole = v(0)
    for _ in range(3):
        pole = identity(p.ctx, pole)
    unit = identity(p.ctx, pole)
    x = p.bracket(pole, pole)
    y = comp2(p.ctx, 3, x, x)
    change = p.bracket(x, y)
    dx, dy = p.bracket(unit, x), p.bracket(unit, y)

    def check_column(first, last, expected):
        col = p.bracket(first, last)
        assert infer(p.ctx, col) == arr(infer(p.ctx, first), first, last)
        assert difference(p.ctx, first, last) == expected

    check_column(comp2(p.ctx, 4, dx, change), dy,
                 {dx[1]: -1, change[1]: -1, dy[1]: 1})
    product = comp2(p.ctx, 3, x, y)
    dproduct = p.bracket(unit, product)
    align = p.bracket(unit, comp2(p.ctx, 3, unit, unit))
    route = comp2(p.ctx, 4, align, comp2(p.ctx, 3, dx, dy))
    check_column(route, dproduct,
                 {align[1]: -1, dx[1]: -1, dy[1]: -1, dproduct[1]: 1})
    check_ctx(p.ctx)


if __name__ == '__main__':
    for k in range(2, 8):
        count = flag_transfer(k)
        print(f'Rank {k}: {count} flags, every rank subset checked, selected coefficient +1.')
    based_identities()
    print('Both based cocycle identities checked as literal six-bracket columns.')
