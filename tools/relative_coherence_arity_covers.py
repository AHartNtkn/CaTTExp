"""Check simultaneous CaTT head parsing and path transport in a nonabelian cover."""
from collections import Counter
from functools import cache
from itertools import permutations, product

from catt import STAR, arr, comp2, infer, src, subst_tm, subst_ty, tgt, v
from ct_suspension import ident

GROUP = tuple(permutations(range(3)))
ONE, SWAP, ROTATE = (0, 1, 2), (1, 0, 2), (1, 2, 0)


def multiply(g, h):
    return tuple(h[i] for i in g)


def presentation():
    ctx = (STAR,) + (arr(STAR, v(0), v(0)),) * 2
    s, t = v(1), v(2)
    unit = ident(ctx, v(0))
    ss = comp2(ctx, 0, s, s)
    tt = comp2(ctx, 0, t, t)
    ttt = comp2(ctx, 0, tt, t)
    sts = comp2(ctx, 0, comp2(ctx, 0, s, t), s)
    for negative, positive in ((ss, unit), (ttt, unit), (sts, tt)):
        base = infer(ctx, negative)
        assert infer(ctx, positive) == base
        ctx += (arr(base, negative, positive),)
    return ctx


def cover(ctx):
    # Deck coordinates multiply in traversal order. The substitution attached
    # to a path depends on its starting sheet, including for the right input.
    lifted = (STAR,) * len(GROUP)
    points = {g: v(i) for i, g in enumerate(GROUP)}
    edges = {}
    for index, step in ((1, SWAP), (2, ROTATE)):
        for g in GROUP:
            edges[g, index] = v(len(lifted))
            lifted += (arr(STAR, points[g], points[multiply(g, step)]),)

    unit_head = ident(ctx, v(0))[:3]
    binary_head = comp2(ctx, 0, v(1), v(2))[:3]

    @cache
    def path(term, g):
        if term[0] == 'v':
            step = {1: SWAP, 2: ROTATE}[term[1]]
            return edges[g, term[1]], multiply(g, step)
        if term[:3] == unit_head:
            return ident(lifted, points[g]), g
        assert term[:3] == binary_head
        left, mid = path(term[3][2], g)
        right, end = path(term[3][4], mid)
        return comp2(lifted, 0, left, right), end

    for g, index in product(GROUP, range(3, 6)):
        negative, end = path(src(ctx, v(index)), g)
        positive, other_end = path(tgt(ctx, v(index)), g)
        assert end == other_end
        base = arr(STAR, points[g], points[end])
        assert infer(lifted, negative) == infer(lifted, positive) == base
        lifted += (arr(base, negative, positive),)
    return lifted, points, edges, path


def main():
    ctx = presentation()
    lifted, points, edges, path = cover(ctx)
    project = ((v(0),) * 6 + (v(1),) * 6 + (v(2),) * 6
               + tuple(v(i) for _ in GROUP for i in range(3, 6)))
    for ty, image in zip(lifted, project, strict=True):
        assert subst_ty(ty, project) == infer(ctx, image)
    s, t = v(1), v(2)
    words = [s, t, ident(ctx, v(0))]
    for length in range(2, 5):
        for letters in product((s, t), repeat=length):
            left = letters[0]
            for letter in letters[1:]:
                left = comp2(ctx, 0, left, letter)
            right = letters[-1]
            for letter in reversed(letters[:-1]):
                right = comp2(ctx, 0, letter, right)
            words.extend((left, right))
    words = tuple(dict.fromkeys(words))
    induced = {term: path(term, ONE)[1] for term in words}
    for term, g in product(words, GROUP):
        answer, end = path(term, g)
        assert end == multiply(g, induced[term])
        assert infer(lifted, answer) == arr(STAR, points[g], points[end])
        assert subst_tm(answer, project) == term
    assert len(points) == 6 and len(edges) == 12 and len(lifted) == 36

    @cache
    def value(term):
        return None if term == v(0) else path(term, ONE)[1]

    @cache
    def parse(a, b):
        assert value(a) == value(b)
        if a[0] == 'coh' and a[:3] == b[:3]:
            labels = tuple(zip(a[3], b[3], strict=True))
            if all(value(x) == value(y) for x, y in labels):
                return ('head', a[:3], tuple(parse(x, y) for x, y in labels))
        return ('generator', a, b)

    def evaluate(tree):
        if tree[0] == 'generator':
            return tree[1:]
        args = [evaluate(child) for child in tree[2]]
        return tuple((*tree[1], tuple(arg[i] for arg in args)) for i in (0, 1))

    counts = Counter()
    for a, b in product(words, repeat=2):
        if value(a) != value(b):
            continue
        parsed = parse(a, b)
        assert evaluate(parsed) == (a, b)
        kind = parsed[0]
        if kind == 'generator' and a[0] == 'coh' and a[:3] == b[:3]:
            kind = 'incompatible labels'
        counts[kind] += 1
    assert min(counts[kind] for kind in ('head', 'generator', 'incompatible labels')) > 0
    print(f'{len(words) * len(GROUP)} typed path lifts, 18 lifted relators, '
          f'{sum(counts.values())} equal-image pairs ({dict(counts)})')


if __name__ == '__main__':
    main()
