"""Check carrier regrouping, lane refinement, and a raw transfer across two pieces."""
from argparse import ArgumentParser
from itertools import combinations, product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, fv_tm, infer, src, tgt, v
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter


def subsets(items):
    for size in range(len(items) + 1):
        for choice in combinations(items, size):
            yield frozenset(choice)


def check_regrouping():
    # Proper ideals in a < b with a third, independent element c.
    atoms = frozenset("abc")
    ideals = {s for s in subsets(atoms) if s and s != atoms and ("b" not in s or "a" in s)}
    minima = frozenset("ac")
    for ideal in ideals:
        cut = ideal & minima
        assert cut in ideals and cut <= minima and cut <= ideal
        for larger in ideals:
            if ideal <= larger:
                assert cut <= larger & minima
    # Over the added bottom there are two incomparable carriers. Above every
    # other ideal there is a singleton fibre. One generator per carrier suffices
    # to check membership of *every* set of generators by inverse image.
    bottom = frozenset()
    carriers = [(bottom, 0), (bottom, 1)] + [(ideal, 0) for ideal in ideals]

    def leq(p, r):
        return p == r or p[0] < r[0]

    def piece(r):
        return {p for p in carriers if leq(p, r)}

    common = {p for p in carriers if p[0] == bottom}
    assert len(common) == 2 and all(not common <= piece(p) for p in common)
    for ideal in ideals:
        r = (ideal, 0)
        regrouped = common | {p for p in carriers if p[0] in ideals and p[0] <= ideal}
        assert regrouped == piece(r)
        for p in regrouped:
            for s in carriers:
                if ideal <= s[0]:
                    assert leq(p, s) == leq(r, s)
    left, right = (frozenset("ab"), 0), (frozenset("c"), 0)
    assert not any({left, right} <= piece(p) for p in carriers)


def paths_in_block(lengths):
    """All chains of distinct states from the input tuple to the output tuple."""
    start = (0,) * len(lengths)
    states = tuple(product(*(range(d + 1) for d in lengths)))

    def extend(path):
        if path[-1] == lengths:
            yield path
        else:
            for state in states:
                if state != path[-1] and all(x <= y for x, y in zip(path[-1], state)):
                    yield from extend(path + (state,))

    return extend((start,))


def strict_image(blocks):
    # The hom on a span is the product of the chain categories on its blocks.
    labels = set()
    start = 0
    for i, path in enumerate(blocks):
        end = start
        labels.add((start, start, (), ()))
        for j in range(i, len(blocks)):
            end += len(blocks[j][0])
            arrows = [tuple((s, t) for k, s in enumerate(chain) for t in chain[k:])
                      for chain in blocks[i:j+1]]
            for factors in product(*arrows):
                source = sum((pair[0] for pair in factors), ())
                target = sum((pair[1] for pair in factors), ())
                labels.add((start, end, source, target))
        start += len(path[0])
    labels.add((start, start, (), ()))
    return frozenset(labels)


def refine(blocks):
    steps = []
    for path in blocks:
        for coordinate in zip(*path):
            steps.append(tuple((x,) for x in dict.fromkeys(coordinate)))
    return tuple(steps)


def check_refinements(lengths):
    minimal = tuple(tuple(dict.fromkeys(((0,), (d,)))) for d in lengths)
    minimum_image = strict_image(minimal)
    table = {}
    for cuts in subsets(range(1, len(lengths))):
        ends = [0, *sorted(cuts), len(lengths)]
        parts = [paths_in_block(lengths[i:j]) for i, j in zip(ends, ends[1:])]
        for blocks in product(*parts):
            image = strict_image(blocks)
            refined = refine(blocks)
            larger = strict_image(refined)
            assert image <= larger and minimum_image <= larger
            assert refine(refined) == refined and len(refined) == len(lengths)
            assert image not in table
            table[image] = larger
    strict_extensions = sum(s < r for s, r in table.items())
    assert strict_extensions and len(set(table.values())) > 1
    for s, r in table.items():
        assert table[r] == r
        assert all(r <= larger for t, larger in table.items() if s <= t)
    return len(table), strict_extensions


def check_transfer(emitter):
    ctx = (STAR, STAR)
    edge = arr(STAR, v(0), v(1))
    ctx += (edge,) * 3
    a, b, c = map(v, (2, 3, 4))
    left, right = arr(edge, a, b), arr(edge, b, c)
    ctx += (left, right, left, right)
    shared_left, shared_right, local_left, local_right = map(v, (5, 6, 7, 8))
    ctx += (arr(left, local_left, shared_left), arr(right, shared_right, local_right))
    terms = (shared_left, shared_right, local_left, local_right, v(9), v(10))
    for cut in range(1, 4):
        check_ctx(ctx)
        sl, sr, ll, lr, change_left, change_right = terms
        u, folded, w = (comp2(ctx, cut, x, y) for x, y in ((ll, sr), (sl, sr), (sl, lr)))
        # Collapse ll and lr to sl and sr. On these two inputs the specialized
        # staircases are one whisker each. The middle writing is fixed by both.
        to_common = comp2(ctx, cut, change_left, sr)
        from_common = comp2(ctx, cut, sl, change_right)
        assert (src(ctx, to_common), tgt(ctx, to_common)) == (u, folded)
        assert (src(ctx, from_common), tgt(ctx, from_common)) == (folded, w)
        result = comp2(ctx, cut + 1, to_common, from_common)
        expected = arr(infer(ctx, u), u, w)
        assert infer(ctx, result) == expected and u != w
        assert {change_left[1], change_right[1]} <= fv_tm(result)
        emitter.check_type(f'descent-{cut}', ctx, result, expected)
        emitter.check_typed(f'descent-{cut}', ctx, result)
        ctx, terms = susp_ctx(ctx), tuple(susp_tm(t) for t in terms)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    check_regrouping()
    results = [check_refinements(lengths) for lengths in ((2, 1), (2, 1, 0), (2, 2, 1))]
    emitter = Emitter()
    check_transfer(emitter)
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Transfers across incomparable carriers.'))
    print(f'Checked regrouping, subdivisions (total, strictly enlarged) {results}, and three raw transfers.')
