"""Check one-event placement, literal lifting, and successive cuts on a folded loop."""
from argparse import ArgumentParser
from collections import deque
from functools import cache
from itertools import combinations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, TypeError_, arr, check_ctx, comp2, infer, maximal_vars,
                  sub_from, subst_tm, subst_ty, tdim_tm, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head
from relative_coherence_hidden_seam import identity
from semistrict_surface_contextual_cut import DecoratedCut


def reachable(initial, rules):
    """States (left path, polygon, right path); rules have single-event sides."""
    seen = {initial}
    queue = deque(seen)
    while queue:
        left, name, right = queue.popleft()
        for (prefix, before, suffix), (pre, after, suf) in rules:
            if name != before or not left.endswith(prefix) or not right.startswith(suffix):
                continue
            outside = left[:len(left) - len(prefix)]
            state = outside + pre, after, suf + right[len(suffix):]
            if state not in seen:
                seen.add(state)
                queue.append(state)
    return seen


def has_cut(states, source, target):
    left = max(len(l) for l, _, _ in states)
    right = max(len(r) for _, _, r in states)
    return left + right < min(len(source), len(target))


def placements():
    # Compare prefix/suffix matching to literal substring rewriting on marked paths.
    count = 0
    for width in range(1, 7):
        word = 'f' * width
        for start in range(width):
            initial = (word[:start], 'A', word[start + 1:])
            for size in range(1, width + 1):
                for i, j in product(range(size), repeat=2):
                    rule = (('f' * i, 'A', 'f' * (size-i-1)),
                            ('f' * j, 'B', 'f' * (size-j-1)))
                    rules = [rule, rule[::-1]]
                    states = reachable(initial, rules)
                    pending = [''.join(initial)]
                    expected = set(pending)
                    while pending:
                        current = pending.pop()
                        for u, v_ in rules:
                            for k in range(width-size+1):
                                if current[k:k+size] == ''.join(u):
                                    dest = current[:k] + ''.join(v_) + current[k+size:]
                                    if dest not in expected:
                                        expected.add(dest)
                                        pending.append(dest)
                    assert {''.join(state) for state in states} == expected
                    common = set(range(width))
                    for reading in expected:
                        common &= {next(k for k, ch in enumerate(reading) if ch in 'AB')}
                    assert has_cut(states, word, word) == bool(common)
                    count += 1
    # This length-changing polygon can shift its placement by a spectator.
    rules = [(('f', 'A', ''), ('', 'B', '')), (('', 'B', ''), ('', 'A', 'f'))]
    states = reachable(('f', 'A', ''), rules)
    assert states == {('f', 'A', ''), ('', 'B', ''), ('', 'A', 'f')}
    assert has_cut(states, 'ffff', 'fff') and not has_cut(states, 'fff', 'ff')
    distinct = 0
    words = [''.join(w) for length in range(1, 5) for w in product('fg', repeat=length)]
    for f, g in product(words, repeat=2):
        bounds = [(i, j) for i in range(min(len(f), len(g)))
                  for j in range(min(len(f), len(g))-i)
                  if f[:i] == g[:i] and f[len(f)-j:] == g[len(g)-j:]]
        for family in combinations(bounds, 2):
            states = [(f[:i], (f[i:len(f)-j], g[i:len(g)-j]), f[len(f)-j:]) for i, j in family]
            ok = all(any(all(i <= k < len(word)-j for i, j in family)
                         for k in range(len(word))) for word in (f, g))
            assert has_cut(states, f, g) == ok
            if len(f) == len(g) and f != g:
                assert ok
            distinct += 1
    print(f'{count} reachable placement queries and {distinct} two-path intersections verified')


def rebracket(ctx, edges, split, reverse):
    arity = tree_ctx(((),) * len(edges))
    row = [v(i) for i in maximal_vars(arity)]
    flat = composite(arity, 0, row)
    grouped = comp2(arity, 0, composite(arity, 0, row[:split]), composite(arity, 0, row[split:]))
    change = head(arity, grouped, flat) if reverse else head(arity, flat, grouped)
    return subst_tm(change, sub_from(arity, ctx, dict(zip(maximal_vars(arity), edges))))


def chart():
    ctx = [STAR] * 5

    def declare(s, t):
        base = infer(tuple(ctx), s)
        assert infer(tuple(ctx), t) == base
        result = v(len(ctx))
        ctx.append(arr(base, s, t))
        return result

    src_edges = [declare(v(i), v(i+1)) for i in range(4)]
    cross = declare(v(1), v(3))
    tgt_edges = [src_edges[0], cross, src_edges[-1]]
    path = lambda edges: composite(tuple(ctx), 0, edges)
    a0 = declare(path(src_edges[:-1]), path(tgt_edges[:-1]))
    a1 = declare(path(src_edges[1:]), path(tgt_edges[1:]))
    b = declare(path(src_edges), path(tgt_edges))

    def placed(left):
        c = tuple(ctx)
        letter = comp2(c, 0, src_edges[0], a1) if left else comp2(c, 0, a0, src_edges[-1])
        enter = rebracket(c, src_edges, 1 if left else len(src_edges)-1, False)
        exit_ = rebracket(c, tgt_edges, 1 if left else len(tgt_edges)-1, True)
        return composite(c, 1, [enter, letter, exit_])

    start, end = placed(True), placed(False)
    r, s, t = declare(start, b), declare(b, end), declare(end, start)
    loop = composite(tuple(ctx), 2, [r, s, t])
    update = declare(loop, loop)
    double = comp2(tuple(ctx), 3, update, update)
    change = declare(double, double)
    higher = declare(change, change)
    terms = [start, b, end, r, s, t, loop, update, double, change, higher,
             comp2(tuple(ctx), 5, identity(tuple(ctx), change), higher)]
    return tuple(ctx), (a0, a1), cross, terms


def fold_chart(ctx, pair):
    ambient, fold = [], []
    for i, ty in enumerate(ctx):
        folded = subst_ty(ty, fold)
        if ty == STAR and i:
            image = v(0)
        elif ty != STAR and ty[1] == STAR and len(ambient) > 1:
            image = v(1)
        elif v(i) == pair[1]:
            image = fold[pair[0][1]]
        else:
            image = v(len(ambient))
            ambient.append(folded)
        assert infer(tuple(ambient), image) == folded
        fold.append(image)
    check_ctx(tuple(ambient))
    return tuple(ambient), tuple(fold)


def checks(agda_dir):
    ctx, pair, cross, terms = chart()
    check_ctx(ctx)
    ambient, fold = fold_chart(ctx, pair)

    @cache
    def lifts(term):
        if term[0] == 'v':
            return tuple(v(i) for i, value in enumerate(fold) if value == term)
        _, arity, ty, args = term
        maximal = maximal_vars(arity)
        answers = []
        for chosen in product(*(lifts(args[i]) for i in maximal)):
            try:
                labels = sub_from(arity, ctx, dict(zip(maximal, chosen)))
            except TypeError_:
                continue
            if tuple(subst_tm(x, fold) for x in labels) == args:
                ans = ('coh', arity, ty, labels)
                infer(ctx, ans)
                answers.append(ans)
        return tuple(answers)

    assert set(lifts(subst_tm(pair[0], fold))) == set(pair)
    for original in terms:
        down = subst_tm(original, fold)
        assert infer(ambient, down) == subst_ty(infer(ctx, original), fold)
        assert lifts(down) == (original,)

    first = DecoratedCut(ctx, {2, 3, 4})
    once = [first.term(term, (), ()) for term in terms]
    middle = tuple(first.lower)
    check_ctx(middle)
    after = {i for i, ty in enumerate(middle) if ty == STAR and first.labels[v(i)][1] == cross[1]}
    second = DecoratedCut(middle, after)
    twice = [second.term(term, (), ()) for term in once]
    local = tuple(second.lower)
    check_ctx(local)
    for ordinal, (original, projected) in enumerate(zip(terms, twice)):
        assert tdim_tm(ctx, original) == tdim_tm(local, projected) + 2
        if ordinal >= 3:
            expected = second.ty(first.ty(infer(ctx, original), (), ()), (), ())
            assert infer(local, projected) == expected
    # Positions separate even though the two labels project to one ambient 2-generator.
    assert len({twice[0], twice[1], twice[2]}) == 3
    names = [first.labels[v(second.labels[t][1])][1] for t in twice[:3]]
    assert names == [pair[1][1], terms[1][1], pair[0][1]]
    if agda_dir is not None:
        out = Emitter()
        for i in [0, 2, 6, 7, 9, 11]:
            original = terms[i]
            out.check_type(f'placed{i}', ctx, original, infer(ctx, original))
            out.check_type(f'folded{i}', ambient, subst_tm(original, fold), subst_ty(infer(ctx, original), fold))
            out.check_eq(f'specialize{i}', original, fold, subst_tm(original, fold))
            expected = STAR if i < 3 else second.ty(first.ty(infer(ctx, original), (), ()), (), ())
            out.check_type(f'cuts{i}', local, twice[i], expected)
        agda_dir.mkdir(parents=True, exist_ok=True)
        (agda_dir / 'EventCorridor.agda').write_text(out.module('EventCorridor', 'Placed, folded and twice-cut judgments.'))
    print(f'{len(terms)} raw terms through degree six lift uniquely and typecheck after both cuts')



def rice_checks(binary):
    from semistrict_surface_exact_boundary import rejected
    from semistrict_surface_local_generators import Checker, FULL, WIDTH_ONE
    with TemporaryDirectory() as temp:
        folder = Path(temp)
        check = Checker(binary.resolve(), folder)
        paths = '(x : *) (f : x -> x)'
        triple = 'comp[comp[f,f],f]'
        wide = f'comp[{triple},f]'
        a_ctx = f'{paths} (a : {triple} -> comp[f,f])'
        (folder / 'Move.catt').write_text('import Heads\n' + """
def openpath = coh [ [e,f,g,h] : comp[comp[comp[e,f],g],h] -> comp[e,comp[comp[f,g],h]] ]
def closepath = coh [ [e,f,g] : comp[e,comp[f,g]] -> comp[comp[e,f],g] ]
""" + f'def placed {a_ctx} = comp[openpath(f,f,f,f),comp[f,[a]],closepath(f,f,f)]\n')
        left, right = 'placed(x,f,a)', 'comp[[a],f]'
        context = (f'{a_ctx} (b : {wide} -> {triple}) (r : {left} -> b)'
                   f' (s : b -> {right}) (t : {right} -> {left})'
                   ' (A : comp[r,s,t] -> comp[r,s,t])')
        flat, nested = 'grouped(A,A,A)', 'h(h(A,A),A)'
        context += f' (Z : {flat} -> {flat}) (K : Z -> Z)'
        fitted, six = 'comp[flat(A,A,A),Z,unflat(A,A,A)]', 'comp[flat(A,A,A),[K],unflat(A,A,A)]'
        for mode in ((), WIDTH_ONE, FULL):
            check.definitions(f'def five {context} : {nested} -> {nested} = {fitted}\n'
                              f'def six {context} : {fitted} -> {fitted} = {six}', mode, 'Move')
        for name, bound, var, fit, unit in [('testfive', nested, 'Z', fitted, f'id({flat})'),
                                             ('testsix', fitted, 'K', six, 'id(Z)')]:
            code = f'def {name} {context} : {bound} -> {bound} = {var}'
            rejected(check.query(code, WIDTH_ONE, 'Move'), 'Check.catt', name)
            check.definitions(code, FULL, 'Move')
            check.equality(fit, var, context, FULL, True, 'Move')
            check.equality(fit, unit, context, FULL, False, 'Move')
        print('Rice verified both fitted raw boundaries and full-insertion classes on the moving polygon')

if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    parser.add_argument('--rice', type=Path)
    args = parser.parse_args()
    placements()
    checks(args.agda_dir)
    if args.rice:
        rice_checks(args.rice)
