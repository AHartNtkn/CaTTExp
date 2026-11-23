"""Check path-indexed restriction at a cut with stationary cycles and mixed attachments."""

from collections import Counter
from functools import cache

from catt import STAR, arr, check_ctx, comp2, infer, maximal_vars, v
from relative_coherence_cut import arity_cut, outer_edge
from relative_coherence_hidden_seam import identity
from semistrict_surface_path_lift import columns


class DecoratedCut:
    """Construct the finite part of the fixed hom needed for the requested terms."""

    def __init__(self, ctx, right):
        self.ctx = ctx
        self.right = right
        self.lower = []
        self.labels = {}

    @cache
    def stationary_word(self, term):
        if term[0] == 'v':
            ty = self.ctx[term[1]]
            assert ty[1] == STAR
            s, t = outer_edge(ty)
            assert (s in self.right) == (t in self.right)
            return (term[1],)
        _, arity, _, args = term
        return tuple(edge for i in columns(arity)[1] for edge in self.stationary_word(args[i]))

    def ty(self, ty, left, right):
        if ty[1] == STAR:
            return STAR
        return arr(self.ty(ty[1], left, right), self.term(ty[2], left, right),
                   self.term(ty[3], left, right))

    @cache
    def term(self, term, left, right):
        if term[0] == 'v':
            slot = term[1]
            ty = self.ty(self.ctx[slot], left, right)
            result = v(len(self.lower))
            self.lower.append(ty)
            self.labels[result] = left, slot, right
            return result
        _, arity, ty, args = term
        right_slots = frozenset(i for i, a in enumerate(arity)
                                if a == STAR and args[i][1] in self.right)
        cut = arity_cut(arity, right_slots)
        _, arrows = columns(arity)
        column, = (j for j, i in enumerate(arrows) if i in cut.indices)
        prefix = tuple(e for i in arrows[:column] for e in self.stationary_word(args[i]))
        suffix = tuple(e for i in arrows[column + 1:] for e in self.stationary_word(args[i]))
        labels = tuple(self.term(args[i], left + prefix, suffix + right) for i in cut.indices)
        if ty[1] == STAR:
            single, = labels
            return single
        return 'coh', cut.context(), cut.type(ty), labels


def fixture():
    ctx = [STAR, STAR]

    def declare(s, t):
        ty = arr(infer(tuple(ctx), s), s, t)
        cell = v(len(ctx))
        ctx.append(ty)
        return cell

    left, right = declare(v(0), v(0)), declare(v(1), v(1))
    f, g = declare(v(0), v(1)), declare(v(0), v(1))
    a = declare(comp2(tuple(ctx), 0, left, f), comp2(tuple(ctx), 0, g, right))
    la = comp2(tuple(ctx), 0, left, a)
    s, t = infer(tuple(ctx), la)[2:]
    b = declare(s, t)
    h = declare(la, b)
    check_ctx(tuple(ctx))
    return tuple(ctx), (left, right, f, g, a, b, h)


def check():
    ctx, (l, r, f, g, a, b, h) = fixture()
    cut = DecoratedCut(ctx, {1})
    stats = Counter()
    for i in range(4):
        for j in range(4):
            left, right = (l[1],) * i, (r[1],) * j
            ai = cut.term(a, left, right)
            s, t = cut.lower[ai[1]][2:]
            assert cut.labels[s] == (left + (l[1],), f[1], right)
            assert cut.labels[t] == (left, g[1], (r[1],) + right)
            hi = cut.term(h, left, right)
            s, t = cut.lower[hi[1]][2:]
            assert s[0] == 'coh'   # A whisker gives the actual raw unary head.
            top, = maximal_vars(s[1])
            assert cut.labels[s[3][top]] == (left + (l[1],), a[1], right)
            assert cut.labels[t] == (left, b[1], right)
            stats['path-indexed generating boundaries'] += 2

            # Form the same exterior context with nested raw whiskerings.
            # Its stationary identity edges have empty words.
            expression = h
            for edge in (identity(ctx, v(0)),) + (l,) * i:
                expression = comp2(ctx, 0, edge, expression)
            for edge in (r,) * j + (identity(ctx, v(1)),):
                expression = comp2(ctx, 0, expression, edge)
            result = cut.term(expression, (), ())
            expected = cut.ty(infer(ctx, expression), (), ())
            assert infer(tuple(cut.lower), result) == expected
            # Read through the nested unary heads to its unique top label.
            while result[0] == 'coh':
                top, = maximal_vars(result[1])
                result = result[3][top]
            assert result == hi
            stats['typed nested boundary projections'] += 1

    check_ctx(tuple(cut.lower))
    assert len(cut.lower) == len(set(cut.labels.values()))
    for label, count in stats.items():
        print(f'{count} {label}')
    print(f'{len(cut.lower)} distinct contextual declarations typechecked')


if __name__ == '__main__':
    check()
