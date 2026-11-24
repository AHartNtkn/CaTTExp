"""Check two successive arity cuts for planar occurrence-wise surface evaluation."""

from argparse import ArgumentParser
from pathlib import Path

from catt import comp2, maximal_vars, ps_dim, sub_from, subst_tm, tree_ctx, v
from ct_suspension import susp_ctx, susp_tm
from partial_cylinder_steiner import trees
from semistrict_surface_insertion_cut import Assertions, check_insertions, cuts, standard


def slots(ctx):
    for i, outer in enumerate(cuts(ctx)):
        for j, inner in enumerate(cuts(outer.context())):
            yield (i, j), outer, inner


class Splices:
    def __init__(self, checks):
        self.checks = checks

    def equal(self, ctx, left, right, case):
        if case != 'root insertions':
            return
        for _, outer, inner in slots(ctx):
            self.checks.equal(inner.context(), inner.term(outer.term(left)),
                              inner.term(outer.term(right)), 'spliced planar slot')


def fold(ctx, cut, terms):
    result = terms[0]
    for term in terms[1:]:
        result = comp2(ctx, cut, result, term)
    return result


def interchange(size):
    ctx = tree_ctx(tuple(tuple(((),) for _ in range(size)) for _ in range(size)))
    labels = list(map(v, maximal_vars(ctx)))
    rows = [labels[i*size:(i+1)*size] for i in range(size)]
    return (ctx, fold(ctx, 0, [fold(ctx, 1, row) for row in rows]),
            fold(ctx, 1, [fold(ctx, 0, list(col)) for col in zip(*rows)]))


def refined_grid(checks):
    coarse, first, second = interchange(2)
    fine = tree_ctx(tuple(tuple(((),) * ((i+j) % 3) for j in range(4)) for i in range(4)))
    entries = {}
    for address, outer, inner in slots(fine):
        local = inner.context()
        suspended = susp_ctx(susp_ctx(local))
        # The last two suspensions embed each maximal local position four
        # declarations later. Invert the actual two cuts to get its fine label.
        global_at = {inner.indices[outer.indices[k]]: v(k) for k in outer.indices
                     if outer.indices[k] in inner.indices}
        lookup = {k: global_at[k-4] for k in maximal_vars(suspended)}
        include = sub_from(suspended, fine, lookup)
        entries[address] = subst_tm(susp_tm(susp_tm(standard(local, 1))), include)
    blocks = []
    for i in (0, 2):
        for j in (0, 2):
            blocks.append(fold(fine, 0, [fold(fine, 1, [entries[a, b] for b in (j, j+1)])
                                         for a in (i, i+1)]))
    labels = sub_from(coarse, fine, dict(zip(maximal_vars(coarse), blocks)))
    for track in (first, second):
        composite = subst_tm(track, labels)
        for _, outer, inner in slots(fine):
            actual = inner.term(outer.term(composite))
            checks.equal(inner.context(), actual, standard(inner.context(), 1), 'substituted array entry')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('catt_strict', type=Path)
    parser.add_argument('--edges', type=int, default=5)
    args = parser.parse_args()
    checks = Assertions()
    for size in range(args.edges + 1):
        for tree in trees(size):
            ctx = tree_ctx(tree)
            for rank in range(ps_dim(ctx), ps_dim(ctx) + 3):
                for _, outer, inner in slots(ctx):
                    body = inner.context()
                    actual = inner.term(outer.term(standard(ctx, rank)))
                    checks.equal(body, actual, standard(body, rank-2), 'standard planar slot')
            for extra in (0, 1):
                check_insertions(Splices(checks), tree, extra)
    for size in (2, 3):
        ctx, left, right = interchange(size)
        for _, outer, inner in slots(ctx):
            body = inner.context()
            event, = maximal_vars(body)
            for track in (left, right):
                restricted = inner.term(outer.term(track))
                checks.equal(body, restricted, v(event), 'array entry after both cuts')
    refined_grid(checks)
    checks.run(args.catt_strict.resolve())


if __name__ == '__main__':
    main()
