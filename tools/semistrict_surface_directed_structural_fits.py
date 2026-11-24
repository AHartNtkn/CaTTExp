"""Check the structural overlaps and the two directions of a width-changing crossing comparison."""
from argparse import ArgumentParser
from functools import cache
from pathlib import Path

from catt import STAR, arr, comp2, infer, maximal_vars, src, sub_from, subst_tm, tgt, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head
from semistrict_surface_directed_power_queries import apply, chart, crossing, row_fit


def rules(prefix):
    a, b, c, outer, inner = [('var', prefix + s) for s in ('a', 'b', 'c', 'C', 'D')]
    one, empty = ('one',), ('empty',)
    return [
        (('seq', ('seq', a, b), c), ('seq', a, ('seq', b, c))),
        (('seq', one, a), a), (('seq', a, one), a),
        (('wing', outer, ('seq', a, b)), ('seq', ('wing', outer, a), ('wing', outer, b))),
        (('wing', outer, one), one),
        (('wing', outer, ('wing', inner, a)), ('wing', ('cat', outer, inner), a)),
        (('wing', empty, a), a),
    ]


def substitute(t, env):
    if t[0] == 'atom':
        return t
    if t[0] == 'var':
        return substitute(env[t], env) if t in env else t
    args = tuple(substitute(x, env) for x in t[1:])
    if t[0] == 'cat':
        return context_word(context_letters(args[0]) + context_letters(args[1]))
    return (t[0], *args)


def context_letters(t):
    if t[0] == 'empty':
        return ()
    if t[0] == 'cat':
        return context_letters(t[1]) + context_letters(t[2])
    return (t,)


def context_word(letters):
    if not letters:
        return ('empty',)
    if len(letters) == 1:
        return letters[0]
    return ('cat', letters[0], context_word(letters[1:]))


def match(left, right, env, two_sided=False):
    left, right = substitute(left, env), substitute(right, env)
    if left == right:
        return True
    if left[0] == 'var':
        env[left] = right
        return True
    if two_sided and right[0] == 'var':
        env[right] = left
        return True
    return left[0] == right[0] and all(match(a, b, env, two_sided)
                                        for a, b in zip(left[1:], right[1:], strict=True))


def positions(t):
    if t[0] in ('var', 'atom'):
        return
    yield (), t
    children = (1, 2) if t[0] == 'seq' else (2,) if t[0] == 'wing' else ()
    for i in children:
        for pos, subterm in positions(t[i]):
            yield (i, *pos), subterm


def replace(t, pos, value):
    if not pos:
        return value
    i = pos[0]
    return (*t[:i], replace(t[i], pos[1:], value), *t[i + 1:])


def freeze(t):
    if t[0] == 'var':
        return ('atom', t[1])
    return (t[0], *(freeze(x) for x in t[1:]))


def reading(t, exterior=()):
    if t[0] == 'one':
        return ()
    if t[0] == 'atom':
        return ((exterior, t),)
    if t[0] == 'seq':
        return reading(t[1], exterior) + reading(t[2], exterior)
    return reading(t[2], exterior + context_letters(t[1]))


def expr_for(items):
    factors = [('wing', context_word(ctx), a) if ctx else a for ctx, a in items]
    if not factors:
        return ('one',)
    result = factors[-1]
    for a in reversed(factors[:-1]):
        result = ('seq', a, result)
    return result


@cache
def terminals(t):
    if t[0] == 'atom':
        return frozenset((t,))
    found = set()
    for pos, subterm in positions(t):
        for lhs, rhs in rules('r'):
            env = {}
            if match(lhs, subterm, env):
                found.update(terminals(replace(t, pos, substitute(rhs, env))))
    return frozenset(found or (t,))


def check_overlaps():
    count = 0
    for i, (outer, contracted) in enumerate(rules('p')):
        for pos, inner in positions(outer):
            for j, (lhs, rhs) in enumerate(rules('q')):
                if not pos and i == j:
                    continue
                env = {}
                if not match(inner, lhs, env, two_sided=True):
                    continue
                peak, first, second = (freeze(substitute(x, env)) for x in
                                       (outer, contracted, replace(outer, pos, rhs)))
                # All formal positive slots fit on one central temporal row.
                row = peak
                while row[0] == 'wing':
                    row = row[2]
                assert all(n[0] != 'wing' for _, n in positions(row))
                target = frozenset((expr_for(reading(peak)),))
                assert terminals(first) == terminals(second) == target
                count += 1
    return count


def distributor(ctx, a, b, wing, expand):
    row = tree_ctx((((), ()), ()))
    x, y, e = map(v, maximal_vars(row))
    block = comp2(row, 0, comp2(row, 1, x, y), e)
    split = comp2(row, 1, comp2(row, 0, x, e), comp2(row, 0, y, e))
    ends = (block, split) if expand else (split, block)
    return apply(ctx, (row, head(row, *ends)), (a, b, wing))


def check_whiskered_row(emitter, actual_ctx, labels):
    row = tree_ctx((((), (), ()), ()))
    a, b, c, e = map(v, maximal_vars(row))

    def seq(x, y):
        return comp2(row, 1, x, y)

    def wing(x):
        return comp2(row, 0, x, e)

    before = seq(seq(a, b), c)
    after = seq(a, seq(b, c))
    first = composite(row, 2, [wing(row_fit(row, before, after)),
                               distributor(row, a, seq(b, c), e, True),
                               seq(wing(a), distributor(row, b, c, e, True))])
    second = composite(row, 2, [distributor(row, seq(a, b), c, e, True),
                                seq(distributor(row, a, b, e, True), wing(c)),
                                row_fit(row, seq(seq(wing(a), wing(b)), wing(c)),
                                        seq(wing(a), seq(wing(b), wing(c))))])
    assert src(row, first) == src(row, second) == wing(before)
    assert tgt(row, first) == tgt(row, second) == seq(wing(a), seq(wing(b), wing(c)))
    for name, x, y in [('rowOverlap', first, second), ('rowOverlapBack', second, first)]:
        cmp = apply(actual_ctx, (row, head(row, x, y)), labels)
        emitter.check_typed(name, actual_ctx, cmp)


def check_rectangle(emitter):
    rect = chart(2, 1)
    a, d, b = map(v, maximal_vars(rect))
    first = comp2(rect, 1, crossing(rect, a, b), comp2(rect, 0, d, tgt(rect, b)))
    last = comp2(rect, 1, comp2(rect, 0, a, src(rect, b)), crossing(rect, d, b))
    direct = crossing(rect, comp2(rect, 1, a, d), b)
    start = comp2(rect, 1, comp2(rect, 0, src(rect, a), b),
                  distributor(rect, a, d, tgt(rect, b), True))
    end = comp2(rect, 1, distributor(rect, a, d, src(rect, b), False),
                comp2(rect, 0, tgt(rect, d), b))
    pieces = [start, row_fit(rect, tgt(rect, start), src(rect, first)), first,
              row_fit(rect, tgt(rect, first), src(rect, last)), last,
              row_fit(rect, tgt(rect, last), src(rect, end)), end]
    split = composite(rect, 2, pieces)
    assert src(rect, split) == src(rect, direct) and tgt(rect, split) == tgt(rect, direct)

    line = tree_ctx(((), (), ()))
    edges = list(map(v, maximal_vars(line)))
    left = composite(line, 0, edges)
    right = comp2(line, 0, edges[0], comp2(line, 0, *edges[1:]))
    fit = head(line, left, right)
    ctx = tree_ctx(((), (), (), ((),)))
    assert ctx[:len(line)] == line
    fixed = v(maximal_vars(ctx)[-1])
    idle = crossing(ctx, fit, fixed)
    other = head(ctx, src(ctx, idle), tgt(ctx, idle))
    for name, x, y in [('idleComparison', idle, other), ('idleReturn', other, idle)]:
        emitter.check_typed(name, ctx, head(ctx, x, y))

    short = v(len(ctx))
    ctx += (arr(STAR, src(ctx, edges[0]), tgt(ctx, edges[-1])),)
    gate = v(len(ctx))
    ctx += (arr(infer(ctx, right), right, short),)
    labels = sub_from(rect, ctx, dict(zip(maximal_vars(rect), (fit, gate, fixed), strict=True)))
    for name, x, y in [('expand', direct, split), ('contract', split, direct)]:
        cmp = head(rect, x, y)
        emitter.check_typed(name + 'Rectangle', rect, cmp)
        actual = subst_tm(cmp, labels)
        s, t = subst_tm(x, labels), subst_tm(y, labels)
        emitter.check_type(name + 'Compound', ctx, actual, arr(infer(ctx, s), s, t))

    new_obj = v(len(ctx))
    ctx += (STAR,)
    wing_edge = v(len(ctx))
    ctx += (arr(STAR, tgt(ctx, tgt(ctx, fixed)), new_obj),)
    first_gate = comp2(ctx, 0, gate, src(ctx, fixed))
    second_gate = comp2(ctx, 0, tgt(ctx, gate), fixed)
    check_whiskered_row(emitter, ctx,
                        (first_gate, second_gate, ident(ctx, tgt(ctx, second_gate)), wing_edge))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    count = check_overlaps()
    emitter = Emitter()
    check_rectangle(emitter)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('DirectedStructuralFits', __doc__)
        (args.agda_dir / 'DirectedStructuralFits.agda').write_text(
            module.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))
    print(f'Checked {count} ordered critical overlaps and both compound rectangle comparisons.')


if __name__ == '__main__':
    main()
