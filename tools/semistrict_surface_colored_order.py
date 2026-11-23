"""Decide width-two and mixed-sign all-width reflection for named Gray scalars."""
from argparse import ArgumentParser
from collections import deque
from itertools import combinations_with_replacement, product
from math import lcm
from pathlib import Path

from catt import arr, comp2, infer, src, tgt, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_braid_order import cube_contexts, missing_translation, raw, surface
from semistrict_surface_three_axis import fitted_exchange, scalar_context


def at_origin(origin, rules):
    """At the opposite reading one prefix crossing is needed to enable a rule."""
    return [(l + (phase != origin), r + (phase != origin)) for phase,l,r in rules
            if phase == origin or phase == origin[::-1]]


def decide(colors, rules):
    all_mixed = True
    for a,b in combinations_with_replacement(colors,2):
        for origin in sorted({a+b, b+a}):
            unary = at_origin(origin,rules)
            missing = missing_translation(unary)
            if missing is not None:
                return (origin, *missing), False
            diffs = {r-l for l,r in unary}
            all_mixed &= any(d > 0 for d in diffs) and any(d < 0 for d in diffs)
    return None, all_mixed


def literal_steps(origin, n, rules):
    for k in range(n+1):
        phase = origin[::-1] if k % 2 else origin
        for p,l,r in rules:
            if p == phase and k+l <= n:
                yield n-l+r


def check_width_two():
    choices = [(p,l,r) for p in ('AB','BA') for l,r in product(range(4),repeat=2)
               if (r-l)%2 == 0 and l != r]
    checks = 0
    for rules in product(choices,repeat=2):
        for origin in ('AB','BA'):
            unary = at_origin(origin,rules)
            for start in range(5):
                assert set(literal_steps(origin,start,rules)) == {start-l+r for l,r in unary if l<=start}
                seen = {start}
                todo = deque([start])
                while todo:
                    n = todo.popleft()
                    for k in literal_steps(origin,n,rules):
                        if k not in seen and k <= 12:
                            seen.add(k)
                            todo.append(k)
                for goal in range(5):
                    answer = raw(start,goal,unary)
                    assert answer == (goal in seen)
                    assert not answer or surface(start,goal,unary)
                    checks += 1
    return checks


def typed_reduce(origin, word, orders):
    """Cancel available same-position powers, tracking colors at both ends."""
    colors = list(origin)
    runs = []
    for pos in word:
        i = pos-1
        a,b = colors[i:i+2]
        period = orders[tuple(sorted((a,b)))]
        count = 1
        if runs and runs[-1][0] == pos:
            count += runs.pop()[1]
        if count != period:
            runs.append((pos,count))
        elif a != b:
            assert period % 2 == 0
        colors[i:i+2] = [b,a]
    return tuple(runs), tuple(colors)


def check_cubes():
    colors = 'ABC'
    orders = dict(zip(combinations_with_replacement(colors,2), (1,2,4,3,2,1), strict=True))
    rules = [(phase,l,r) for (a,b),d in orders.items() for phase in {a+b,b+a}
             for l,r in ((0,d),(d,0))]
    assert decide(colors,rules) == (None,True)
    rules = [rule for rule in rules if rule[0] != 'BA']
    assert decide(colors,rules)[0][0] == 'BA'
    for origin in product(colors,repeat=3):
        d = lcm(*(orders[tuple(sorted(p))] for p in combinations_with_replacement(origin,2)))
        red = lambda w: typed_reduce(origin,w,orders)
        X,Y = (1,2,1),(2,1,2)
        current = red(Y)
        for l,r in cube_contexts(d):
            assert red(l+X+r) == current
            current = red(l+Y+r)
        assert current == red(X)
    return len(colors)**3


def phase_boundary():
    ctx = scalar_context(2)
    _, ab = fitted_exchange(ctx,v(1),v(2))
    _, ba = fitted_exchange(ctx,v(2),v(1))
    assert src(ctx,ab) == tgt(ctx,ba) != src(ctx,ba) == tgt(ctx,ab)
    loops = [comp2(ctx,2,s,t) for s,t in ((ab,ba),(ba,ab))]
    empty = [identity(ctx,src(ctx,s)) for s in (ab,ba)]
    ty = infer(ctx,loops[0])
    ctx += (arr(ty,empty[0],loops[0]),arr(ty,loops[0],empty[0]))
    emitter = Emitter()
    for index, label in ((3,'increase-ab'),(4,'decrease-ab')):
        emitter.check_type(label,ctx,v(index),ctx[index])
    old = arr(infer(ctx,loops[1]),empty[1],loops[1])
    g = emitter.ctx(ctx)
    emitter.checks.append(f'opposite-order : {g} ⊢ty {emitter.ty(old)}\n'
                          f'opposite-order = from-just (checkTy {g} (from-just (checkCtx {g}))'
                          f' {emitter.ty(old)})\n')
    return emitter


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--colors', help='distinct single-character scalar names')
    parser.add_argument('--rule', action='append', default=[], metavar='AB:LEFT:RIGHT')
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.colors is not None:
        if not args.colors or len(set(args.colors)) != len(args.colors):
            parser.error('colors must be nonempty and distinct')
        rules = []
        for entry in args.rule:
            try:
                phase,l,r = entry.split(':')
                l,r = int(l),int(r)
                if (len(phase) != 2 or set(phase)-set(args.colors) or min(l,r)<0
                        or (phase[0]!=phase[1] and (l-r)%2)):
                    raise ValueError
                rules.append((phase,l,r))
            except ValueError:
                parser.error('each rule needs declared names and parallel natural-number faces')
        failure, mixed = decide(args.colors,rules)
        if failure:
            p,s,t = failure
            print(f'Old type fails at {p}: {s} -> {t}.')
        elif mixed:
            print('All old four-types reflect at every width.')
        else:
            print('All old width-two four-types reflect. The all-pairs mixed-sign criterion does not apply.')
        return
    print(f'{check_width_two():,} literal two-color comparisons checked.')
    print(f'{check_cubes()} typed reverse cubes checked with nonuniform crossing orders.')
    if args.agda:
        emitter = phase_boundary()
        module = emitter.module(args.agda.stem, 'Two named scalars and opposite crossing orders.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n','open import CaTTExp.Gray.Pure\n'))


if __name__ == '__main__':
    main()
