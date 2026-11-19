"""Verify the single-top correspondence and every nested boundary cut for any depth."""
import argparse
from collections import Counter

from gray_globe_attachments import blocks
from gray_globe_comparison import face
from gray_globe_factorizations import rank, truncate
from gray_globe_section import EMPTY_ROW, cells, row_map
from gray_path_wedge import compose


def copy_label(g, a, side):
    p, q = g
    return ((a, side) if p[0] == a else p), q


def cylinder(c, a):
    """Tableau of the image of I tensor the characteristic globe of c."""
    rows = []
    for k in range(len(c)+1):
        row = []
        for side in (0, 1):
            cap = [copy_label(g, a, side) for g in c[k][side]] if k < len(c) else []
            moving = [((a+1, 2), q) for p, q in c[k-1][1-side] if p[0] == a] if k else []
            row.append(tuple(sorted(cap + moving)))
        rows.append(tuple(row))
    return tuple(rows)


def syntax_check():
    """Compare both real 3-term boundaries with the depth-one formula."""
    from catt import comp2, subst_tm
    from gray_globe_pure_extension import extend, raise_argument, two_by_two

    a = 2
    base = two_by_two()
    ctx, names, chosen = extend(base, (2, 2), 0, 3, None)
    substitutions = [[names[copy_label(g, a, side)] for g in base[1]] for side in (0, 1)]
    total = 0
    for c, term in base[2].items():
        if len(c) != a+2 or not any(rank(g) == (a, 1) for g in c[-1][0]):
            continue
        copies = [subst_tm(term, sigma) for sigma in substitutions]
        caps = []
        for side in (0, 1):
            z = face(c, side)
            pure, = (g for g in z[-1][0] if rank(g) == (a, 0))
            moving = names[(a+1, 2), pure[1]]
            variable = names[copy_label(pure, a, 0)]
            cap = raise_argument(ctx, subst_tm(base[2][z], substitutions[0]), variable, moving)
            assert cap == chosen[cylinder(z, a)]
            caps.append(cap)
        actual = tuple(chosen[face(cylinder(c, a), side)] for side in (0, 1))
        assert actual == (comp2(ctx, a, copies[0], caps[1]), comp2(ctx, a, caps[0], copies[1]))
        total += 1
    print(f'Checked both literal depth-one boundaries for all {total} obligations')


def check(a, n):
    old = cells((a, n)) - {()}
    new = cells((a+1, n)) - {()}
    actual = {w for w in new if len(w[-1][0]) == 1 and rank(w[-1][0][0])[0] == a+1}
    expected = set()
    degrees = Counter()
    cuts = 0
    for c in old:
        e = len(c)-1
        marked = [g for g in c[-1][0] if rank(g)[0] == a]
        if not marked:
            continue
        g, = marked
        w = cylinder(c, a)
        assert w not in expected
        expected.add(w)
        assert w[-1][0] == (((a+1, 2), g[1]),)
        degrees[e-a] += 1
        for side in (0, 1):
            current = row_map(c, 0, lambda h: copy_label(h, a, side))
            for j in range(a, e):
                moving = cylinder(truncate(c, j, 1-side), a)
                left, right = (moving, current) if side else (current, moving)
                assert left[:j] == right[:j] and left[j][1] == right[j][0]
                current = compose(left + (EMPTY_ROW,)*(e+1-len(left)),
                                  right + (EMPTY_ROW,)*(e+1-len(right)), j)
                assert blocks(current, (a+1, j-a)) == (left, right)
                cuts += 1
            assert current == face(w, side)
    assert expected == actual
    print(f'D^{a+1} tensor D^{n}: {len(actual)} single-top cells in bijection, '
          f'{cuts} forced boundary cuts; counts by depth {dict(sorted(degrees.items()))}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('a', type=int)
    parser.add_argument('n', type=int)
    parser.add_argument('--syntax', action='store_true', help='also check literal boundaries on the (2,2) core')
    args = parser.parse_args()
    if min(args.a, args.n) < 1:
        parser.error('both original globe dimensions must be positive')
    check(args.a, args.n)
    if args.syntax:
        syntax_check()
