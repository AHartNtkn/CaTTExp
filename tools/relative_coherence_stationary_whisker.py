"""Exact four-dimensional partial action of an outer whisker fixed through dimension one."""
from argparse import ArgumentParser
from functools import cache, reduce
from pathlib import Path

from catt import (arr, comp2, disc_tree, glue_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, tdim_tm, tgt, tree_ctx, v)
from emit_agda import Emitter
from gray_globe_branch_comparisons import cylinder
from gray_globe_exterior_actions import certificate
from gray_partial_cylinder_sections import selections
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head, string_tree


def fold(items, op):
    return reduce(op, items)


def at_chart(ctx, tree, labels, build):
    old = tree_ctx(tree)
    top = tuple(map(v, maximal_vars(old)))
    a, b = build(old, *top)
    sigma = sub_from(old, ctx, dict(zip(maximal_vars(old), labels, strict=True)))
    return tuple(subst_tm(head(old, s, t), sigma) for s, t in ((a, b), (b, a)))


class Whisker:
    def __init__(self, left):
        self.left = left

    def w(self, ctx, edge, term):
        a, b = (edge, term) if self.left else (term, edge)
        return comp2(ctx, 0, a, b)

    def chart(self, ctx, edge, inner, pair, build):
        if self.left:
            return at_chart(ctx, disc_tree(1)+inner, (edge, *pair), build)
        return at_chart(ctx, inner+disc_tree(1), (*pair, edge),
                        lambda g, a, b, e: build(g, e, a, b))

    @cache
    def distributor(self, ctx, edge, a, b):
        d = tdim_tm(ctx, a)
        def terms(g, e, x, y):
            return (comp2(g, d-1, self.w(g, e, x), self.w(g, e, y)),
                    self.w(g, e, comp2(g, d-1, x, y)))
        return self.chart(ctx, edge, glue_tree(d, d-1, d), (a, b), terms)

    def square(self, ctx, edge, x, h, plus):
        # The two 3-face distributors bound one ordinary four-dimensional pasting.
        def terms(g, e, a, b):
            cell, rail = (b, a) if plus else (a, b)
            def pair(y):
                return (rail, y) if plus else (y, rail)
            def dis(y):
                return self.distributor(g, e, *pair(y))[int(plus)]
            outside = comp2(g, 2, *(self.w(g, e, t) for t in pair(cell)))
            inside = self.w(g, e, comp2(g, 2, *pair(cell)))
            if plus:
                return comp2(g, 3, dis(src(g, cell)), outside), comp2(g, 3, inside, dis(tgt(g, cell)))
            return comp2(g, 3, outside, dis(tgt(g, cell))), comp2(g, 3, dis(src(g, cell)), inside)
        pair = (h, x) if plus else (x, h)
        inner = glue_tree(3, 2, 4) if plus else glue_tree(4, 2, 3)
        return self.chart(ctx, edge, inner, pair, terms)


def standard(items):
    return fold(items, lambda a, b: (a, b))


def brackets(ctx, terms, shape):
    if isinstance(shape, int):
        return terms[shape]
    a, b = shape
    return comp2(ctx, 3, brackets(ctx, terms, a), brackets(ctx, terms, b))


def association(ctx, word, a, b):
    if a == b:
        return []
    return [at_chart(ctx, string_tree(3, [4]*len(word)), word,
                     lambda g, *args: (brackets(g, args, a), brackets(g, args, b)))]


def surround(items, core, suffix, op):
    if items:
        core = op(fold(items, op), core)
    return reduce(op, suffix, core)


def replace(ctx, word, start, length, new, proof):
    """Rebracket a temporal string around a subword and apply the two typed rewrites."""
    end = start + length
    def shape(size, count):
        ids = list(range(size))
        return surround(ids[:start], standard(ids[start:start+count]), ids[start+count:],
                        lambda x, y: (x, y))
    result = association(ctx, word, standard(range(len(word))), shape(len(word), length))
    sides = tuple(surround(word[:start], p, word[end:], lambda a, b: comp2(ctx, 3, a, b))
                  for p in proof)
    result.append(sides)
    word = word[:start] + new + word[end:]
    result.extend(association(ctx, word, shape(len(word), len(new)), standard(range(len(word)))))
    return word, result


def pasted(left, marks):
    op = Whisker(left)
    tree = glue_tree(1, 0, 4) if left else glue_tree(4, 0, 1)
    old = tree_ctx(tree)
    slots = maximal_vars(old)
    e, x = slots if left else reversed(slots)
    ctx, minus, changes = cylinder(old, marks)
    plus = [v(m[1]+1) if i in marks else m for i, m in enumerate(minus)]
    edge = minus[e]
    s, t = src(old, v(x))[1], tgt(old, v(x))[1]
    low = (tgt(old, v(s))[1], src(old, v(s))[1])
    rail = [changes.get(i) for i in low]
    W = lambda y: op.w(ctx, edge, y)
    product = lambda a, b: comp2(ctx, 3, a, b)

    def ordered(y, side):
        return (rail[side], y) if side else (y, rail[side])
    def pad_low(y, side, distribute=False):
        if rail[side] is None:
            return W(y) if distribute else y
        a, b = ordered(y, side)
        return comp2(ctx, 2, W(a), W(b)) if distribute else comp2(ctx, 2, a, b)
    def distributor(i, side):
        y = (minus, plus)[side][i]
        return op.distributor(ctx, edge, *ordered(y, side))[side]
    def change_word(i):
        return (([distributor(i, 0)] if rail[0] else []) + [W(changes[i])] +
                ([distributor(i, 1)] if rail[1] else []))

    caps, routes = [], []
    # Align each cap to the whiskered original cap with the same exterior distributors.
    for side, copy in enumerate((minus, plus)):
        pole = (t, s)[side]
        ux = pad_low(copy[x], side, True)
        word = [ux]
        if pole in marks:
            h = change_word(pole)
            shape = ((standard(range(len(h))), len(h)) if side else
                     (0, standard(range(1, len(h)+1))))
            word = h+[ux] if side else [ux]+h
        else:
            shape = 0
        caps.append(brackets(ctx, word, shape))
        steps = association(ctx, word, shape, standard(range(len(word))))
        if rail[side]:
            square = op.square(ctx, edge, copy[x], rail[side], bool(side))
            inner = W(pad_low(copy[x], side))
            start = len(word)-2 if side else 0
            new = [inner, distributor(t, side)] if side else [distributor(s, side), inner]
            word, more = replace(ctx, word, start, 2, new, square)
            steps += more
        if pole in marks:
            inner = pad_low(copy[x], side)
            a, b = (changes[pole], inner) if side else (inner, changes[pole])
            start = int(bool(rail[0]))
            word, more = replace(ctx, word, start, 2, [W(product(a, b))],
                                 op.distributor(ctx, edge, a, b))
            steps += more
        routes.append(steps)
    core = surround([distributor(s, 0)] if rail[0] else [], W(changes[x]),
                    [distributor(t, 1)] if rail[1] else [], product)
    steps = [p for p, _ in routes[0]] + [core] + [q for _, q in reversed(routes[1])]
    term = fold(steps, lambda a, b: comp2(ctx, 4, a, b))
    wanted = arr(infer(ctx, caps[0]), *caps)
    assert infer(ctx, term) == wanted
    assert top_counts(ctx, term) == {changes[x][1]: 1}
    return ctx, term, wanted


def run(dest):
    for left in (False, True):
        old = tree_ctx(glue_tree(1, 0, 4) if left else glue_tree(4, 0, 1))
        count = 0
        for marks in selections(old):
            if not marks or min(tdim_tm(old, v(i)) for i in marks) < 2:
                continue
            ctx, term, wanted = pasted(left, marks)
            count += 1
            if dest and left and len(marks) == 5:
                emitter = Emitter()
                certificate(emitter, ctx)('outer-whisker-action', term, wanted)
                dest.write_text(emitter.module(dest.stem, 'A stationary outer whisker with both two-poles selected.'))
        print(f'Outer whisker on the {"left" if left else "right"}: {count} exact five-terms.', flush=True)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    run(parser.parse_args().agda)
