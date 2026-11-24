"""Check the Gray last-rank exceptions and the matrix model for a square guard."""
from collections import Counter
from functools import cache
from itertools import combinations, product

from partial_cylinder_steiner import globular, trees
from semistrict_surface_signed_width_two import Attachment, Movies, Presentation, Rule


def row(columns, rank, side):
    if not columns:
        return [()] if rank == 0 else []
    first, *rest = columns
    result = []
    for d in range(rank+1):
        excluded = {faces[1-side] for _, dim, *faces in first if dim == d+1}
        heads = [x for x, dim, _, _ in first if dim == d and x not in excluded]
        tails = row(rest, rank-d, side ^ (d % 2))
        result.extend(((d, x), *tail) for x, tail in product(heads, tails))
    return result


def short_assignments(column):
    # A functor into the one-object monoid of lengths gives parallel
    # 1-generators joined by a 2-generator equal length. Only positivity
    # matters to the zero test. Enumerate every such assignment.
    cells = [x for x, d, _, _ in column if d == 1]
    for flags in product((False, True), repeat=len(cells)):
        moving = {x for x, flag in zip(cells, flags) if flag}
        if all((s in moving) == (t in moving) for s, t in
               ((s, t) for _, d, s, t in column if d == 2)):
            yield moving


def gives_zero(chain, i, j, left, right):
    return any(w[i][0] == w[j][0] == 1 and w[i][1] in left and w[j][1] in right
               for w in chain)


def check_rows():
    totals = Counter()
    for size in range(1, 9):
        for arity in trees(size):
            cols = [globular(t) for t in arity]
            h = sum(max(d for _, d, _, _ in c) for c in cols)
            if h not in (2, 3) or len(cols) < 2:
                continue
            lo, hi = (row(cols, 2, k) for k in (0, 1))
            for i, j in combinations(range(len(cols)), 2):
                for left, right in product(short_assignments(cols[i]), short_assignments(cols[j])):
                    a = gives_zero(lo, i, j, left, right)
                    b = gives_zero(hi, i, j, left, right)
                    assert a == b
                    if h == 2:
                        # The generic 3-total is a nontrivial map exactly for
                        # a rectangle whose two active sides both move.
                        assert a == bool(left and right)
                    totals[h, a] += 1
    print('Signed tableau tests by local height and zero value:', dict(sorted(totals.items())))


def multiply(a, b):
    return tuple(tuple(sum(x*y for x, y in zip(r, col)) for col in zip(*b)) for r in a)


def kronecker(a, b):
    return tuple(tuple(x*y for x in row for y in inner) for row in a for inner in b)


@cache
def eye(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def zero(n):
    return tuple((0,)*n for _ in range(n))


def crossing(m, n):
    dim = 2**(m+n)
    return zero(dim) if m and n else eye(dim)


def word_matrix(w):
    value = eye(4)
    for x in w:
        letter = ((3, x+1, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))
        value = multiply(value, letter)
    return value


def check_matrices():
    for a, b, c in product(range(3), repeat=3):
        # Both signed subdivisions of a spatial rectangle. Each temporal
        # whisker acts by tensoring the matrix with a stationary identity.
        assert crossing(a, b+c) == multiply(kronecker(crossing(a, b), eye(2**c)),
                                            kronecker(eye(2**b), crossing(a, c)))
        assert crossing(a+b, c) == multiply(kronecker(eye(2**a), crossing(b, c)),
                                            kronecker(crossing(a, c), eye(2**b)))
    words = [w for n in range(6) for w in product(range(2), repeat=n)]
    matrices = {word_matrix(w) for w in words}
    assert len(matrices) == len(words)
    assert {multiply(crossing(1, 1), x) for x in matrices} == {zero(4)}

    # At the same literal old boundary, compare the surface answer with the
    # independently computed monoid values of its two parallel 3-cells.
    ab = ((0, 'a'), (1, 'b'))
    ba = ab[::-1]
    base = Presentation({'f': (0, 1), 'g': (1, 2)}, {'a': ('f', 'f'), 'b': ('g', 'g')},
                        [Rule('fg', ab, ab), Rule('fg', ab, ab), Rule('fg', ab, ba)])
    def movie(word):
        return [(i, 0) for i in word]
    model = Movies(base, 'fg', [Attachment('fg', ba, [('swap', 0), *movie((0, 1))],
                                            [('swap', 0), *movie((1, 0))])])
    counts = Counter()
    for w, v in product([p for p in words if len(p) <= 3], repeat=2):
        actual = model.compare(ab, movie(w), movie(v))['surface']
        expected = (len(w) == len(v) and sum(w) == sum(v)
                    and all(sum(w[:i]) <= sum(v[:i]) for i in range(len(w))))
        assert actual == expected
        truncated = word_matrix(w) == word_matrix(v)
        assert truncated == (w == v)
        counts[actual, truncated] += 1
    print(f'Checked both rectangle subdivisions for 27 triples and {len(words)} distinct words.')
    print('Guarded judgments by full and restricted answers:', dict(counts))


if __name__ == '__main__':
    check_rows()
    check_matrices()
