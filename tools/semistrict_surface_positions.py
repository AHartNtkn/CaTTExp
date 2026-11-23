"""Finite checks for Researcher Response 4 in semistrict-surface-conservativity.md."""

from collections import Counter
from functools import cache
from itertools import product

from catt import STAR, arr, comp2, disc_tree, glue_tree, infer, maximal_vars, src, sub_from, subst_tm, tgt, tree_ctx, v
from catt_unit_ordered_exchange import temporal_words
from gray_globe_comparison import atom, globe
from relative_coherence_hidden_seam import identity


def vertical(left, right):
    return {p: left.get(p, ()) + right.get(p, ()) for p in left.keys() | right.keys()}


def horizontal(left, right):
    return {str(i) + p: word for i, table in enumerate((left, right)) for p, word in table.items()}


def label(column, step):
    return {"": ((column, step, 0), (column, step, 1)), "01": ((column, step, 2),)}


@cache
def shapes(columns):
    if len(columns) == 1:
        return [columns[0]]
    return [(left, right) for cut in range(1, len(columns))
            for left in shapes(columns[:cut]) for right in shapes(columns[cut:])]


def leaves(tree, prefix=""):
    if isinstance(tree, int):
        yield prefix, tree
    else:
        yield from leaves(tree[0], prefix + "0")
        yield from leaves(tree[1], prefix + "1")


def check_cuts(counts):
    @cache
    def value(tree, start, end):
        # Read the strict path separately in each active column.
        expected = {}
        for (address, column), lo, hi in zip(leaves(tree), start, end):
            if lo < hi:
                for suffix in ("", "01"):
                    expected[address + suffix] = tuple(token for j in range(lo, hi)
                                                       for token in label(column, j)[suffix])

        if isinstance(tree, int):
            result = {}
            for j in range(start[0], end[0]):
                result = vertical(result, label(tree, j))
        else:
            left, right = tree
            cut = len(list(leaves(left)))
            result = horizontal(value(left, start[:cut], end[:cut]),
                                value(right, start[cut:], end[cut:]))
            counts["spatial cuts"] += 1
        assert result == expected

        for mid in product(*(range(a, b + 1) for a, b in zip(start, end))):
            if mid == start:
                earlier, later = {}, result
            elif mid == end:
                earlier, later = result, {}
            else:
                earlier, later = value(tree, start, mid), value(tree, mid, end)
            assert vertical(earlier, later) == expected
            counts["temporal cuts"] += 1
        return result

    for size in range(1, 4):
        columns = tuple(range(size))
        # -1 is an identity leaf. It has a single state and no generating steps.
        for seq in [columns] + [columns[:i] + (-1,) + columns[i:] for i in range(size + 1)]:
            states = list(product(*(range(3 if column >= 0 else 1) for column in seq)))
            for tree in shapes(seq):
                for start, end in product(states, repeat=2):
                    if all(a <= b for a, b in zip(start, end)):
                        value(tree, start, end)


def check_projections(counts):
    for sizes in product(range(4), repeat=3):
        for generators in product(*(globe(size) for size in sizes)):
            rows = atom(generators)
            for index, generator in enumerate(generators):
                def augment(chain):
                    return tuple(sorted(term[index] for term in chain
                                        if all(g[0] == 0 for j, g in enumerate(term) if j != index)))

                projected = tuple((augment(source), augment(target)) for source, target in rows)
                single = tuple(tuple(tuple(term[0] for term in side) for side in row)
                               for row in atom((generator,)))
                assert projected == single + (((), ()),) * (len(rows) - len(single))
                counts["tensor atom projections"] += 1


def check_unit_whiskers():
    ctx = tree_ctx(disc_tree(2))
    top, = maximal_vars(ctx)
    cell = v(top)
    left_unit = identity(ctx, src(ctx, src(ctx, cell)))
    right_unit = identity(ctx, tgt(ctx, tgt(ctx, cell)))
    padded = comp2(ctx, 0, comp2(ctx, 0, left_unit, cell), right_unit)
    infer(ctx, padded)

    def read(term):
        if term == cell:
            return {"": ("token",)}
        arity, arguments = term[1], term[3]
        first, second = maximal_vars(arity)
        if arity == tree_ctx(glue_tree(1, 0, 2)):
            return horizontal({}, read(arguments[second]))
        assert arity == tree_ctx(glue_tree(2, 0, 1))
        return horizontal(read(arguments[first]), {})

    assert read(padded) == {"01": ("token",)} and read(padded) != read(cell)


def check_folded_square():
    loop_type = arr(STAR, v(0), v(0))
    ctx = (STAR, loop_type, arr(loop_type, v(1), v(1)))
    square = tree_ctx(glue_tree(2, 0, 2))
    first, second = maximal_vars(square)
    fold = sub_from(square, ctx, {first: v(2), second: v(2)})
    left, right = (subst_tm(term, fold) for term in temporal_words(square, v(first), v(second), 0, 1))
    assert left != right and infer(ctx, left) == infer(ctx, right)
    assert src(ctx, left) == tgt(ctx, left) == comp2(ctx, 0, v(1), v(1))


if __name__ == "__main__":
    counts = Counter()
    check_cuts(counts)
    check_projections(counts)
    check_folded_square()
    check_unit_whiskers()
    for kind, count in sorted(counts.items()):
        print(f"{count:,} {kind}")
    print("Double identity whiskering moves the walking 2-cell token to address 01.")
    print("Folded square has distinct words at the same literal boundary.")
