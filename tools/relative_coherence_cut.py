"""Restrict a typed CaTT term to the branch crossing a directed object cut."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, fv_tm, infer, subst_tm,
                  subst_ty, tdim, tree_ctx, ucomp, v)
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from partial_cylinder_steiner import trees
from relative_coherence_hidden_seam import identity


def outer_edge(ty):
    if ty == STAR:
        return None
    while ty[1] != STAR:
        ty = ty[1]
    return ty[2][1], ty[3][1]


class Cut:
    def __init__(self, ctx, right):
        self.ctx = ctx
        self.right = frozenset(right)
        self.indices = {}
        for i, ty in enumerate(ctx):
            ends = outer_edge(ty)
            if ends is None:
                continue
            source, target = (x in self.right for x in ends)
            if source and not target:
                raise ValueError("a generating arrow points backwards across the cut")
            if not source and target:
                self.indices[i] = len(self.indices)

    def context(self):
        return tuple(self.type(self.ctx[i]) for i in self.indices)

    def type(self, ty):
        if ty[1] == STAR:
            return STAR
        return arr(self.type(ty[1]), self.term(ty[2]), self.term(ty[3]))

    @cache
    def term(self, t):
        if t[0] == 'v':
            return v(self.indices[t[1]])
        _, arity, boundary, args = t
        right = frozenset(i for i, ty in enumerate(arity)
                          if ty == STAR and args[i][1] in self.right)
        generic = arity_cut(arity, right)
        if not generic.indices:
            raise ValueError("term does not cross the cut")
        labels = tuple(self.term(args[i]) for i in generic.indices)
        if boundary[1] == STAR:
            selected, = labels
            return selected
        return ('coh', generic.context(), generic.type(boundary), labels)


@cache
def arity_cut(arity, right):
    return Cut(arity, right)


def top_counts(ctx, term):
    if term[0] == 'v':
        return Counter({term[1]: 1})
    _, arity, ty, args = term
    counts = Counter()
    for slot, value in zip(arity, args):
        if tdim(slot) == tdim(ty):
            counts.update(top_counts(ctx, value))
    return counts


def shape_checks(max_edges):
    totals = Counter()
    for edges in range(1, max_edges + 1):
        for tree in trees(edges):
            ctx = tree_ctx(tree)
            objects = [i for i, ty in enumerate(ctx) if ty == STAR]
            for j, child in enumerate(tree):
                cut = Cut(ctx, objects[j + 1:])
                lower = cut.context()
                assert lower == tree_ctx(child)
                target = susp_ctx(lower)
                poles = Cut(target, (1,))
                # Evaluate each inactive slot at its pole's identity tower.
                sigma = []
                for i, ty in enumerate(ctx):
                    if ty == STAR:
                        value = v(int(i in cut.right))
                    elif i in cut.indices:
                        value = susp_tm(v(cut.indices[i]))
                    else:
                        value = identity(target, subst_tm(ty[2], sigma))
                    assert infer(target, value) == subst_ty(ty, sigma)
                    sigma.append(value)
                for raised in (False, True):
                    term = ucomp(ctx)
                    if raised:
                        term = identity(ctx, term)
                    result = cut.term(term)
                    assert infer(lower, result) == cut.type(infer(ctx, term))
                    assert fv_tm(result) == {new for old, new in cut.indices.items()
                                             if old in fv_tm(term)}
                    assert result == poles.term(subst_tm(term, sigma))
                    assert poles.term(susp_tm(result)) == result
                    # At rank one the sole surviving edge becomes an object.
                    counts = top_counts(ctx, term)
                    assert top_counts(lower, result) == {
                        new: counts[old] for old, new in cut.indices.items() if counts[old]}
                    totals['terms'] += 1
                totals['cuts'] += 1
            totals['trees'] += 1
    print(f"{totals['trees']} nonempty trees, {totals['cuts']} root cuts,"
          f" {totals['terms']} typed projections and substitution equations.")


def loop_checks(agda):
    # Arbitrary arity-changing weak attachment upstairs in the active hom.
    from relative_coherence_substitution import triangle_term
    base, triangle = triangle_term()
    target = susp_ctx(base)
    cut = Cut(target, (1,))
    check_ctx(target)
    assert cut.context() == base and cut.term(susp_tm(triangle)) == triangle

    # A genuine asymmetric base: f and g are parallel; only a : f -> g.
    ctx = (STAR, STAR, arr(STAR, v(0), v(1)), arr(STAR, v(0), v(1)))
    ctx += (arr(ctx[2], v(2), v(3)),)
    over = susp_ctx(ctx)
    # Add a true generating endoloop on each side and a 2-endoloop on each.
    # Their positive powers need not be weak units.
    loops = [v(len(over)), v(len(over) + 1)]
    over += tuple(arr(STAR, v(i), v(i)) for i in range(2))
    repeats = [v(len(over)), v(len(over) + 1)]
    over += tuple(arr(infer(over, p), p, p) for p in loops)
    check_ctx(over)
    cut = Cut(over, (1,))
    assert cut.context() == ctx
    emitter = Emitter()
    for power in range(1, 8):
        pads = []
        for letter in repeats:
            pad = letter
            for _ in range(1, power):
                pad = comp2(over, 1, pad, letter)
            pads.append(pad)
        term = comp2(over, 0, pads[0], comp2(over, 0, susp_tm(v(4)), pads[1]))
        lower = cut.term(term)
        assert infer(ctx, lower) == cut.type(infer(over, term))
        assert top_counts(ctx, lower) == {4: 1}
        # The source and target can acquire genuine unary coherence heads.
        source, end = infer(ctx, lower)[2:]
        assert (top_counts(ctx, source), top_counts(ctx, end)) == ({2: 1}, {3: 1})
        if power == 3:
            emitter.check_type('mixed', over, term, infer(over, term))
            emitter.check_type('projected', ctx, lower, arr(infer(ctx, source), source, end))
    print("Arbitrary-attachment suspension recovered literally;"
          " seven positive loop powers on both sides of a one-way generator checked.")
    if agda:
        agda.write_text(emitter.module(agda.stem, "Directed cut across two nontrivial endohoms."))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--max-edges', type=int, default=6)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    shape_checks(args.max_edges)
    loop_checks(args.agda)
