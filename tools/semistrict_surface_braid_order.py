"""Decide scalar width-two reflection and the mixed-sign all-width criterion."""
import argparse
from itertools import product
from math import gcd
from pathlib import Path

from catt import arr, comp2, infer, src, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_scalar_cube import cube_terms
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_three_axis import fitted_crossing
from semistrict_surface_triple_attachments import one_counter


def raw(start, goal, rules):
    transitions = {((0,l), (0,r), False) for l,r in rules}
    return one_counter((0,start), (0,goal), transitions)


def surface(start, goal, rules):
    diffs = {r-l for l,r in rules if r != l}
    delta = goal - start
    if not diffs or not delta:
        return delta == 0
    if min(diffs) < 0 < max(diffs):
        return delta % gcd(*diffs) == 0
    if max(diffs) < 0:
        diffs = {-d for d in diffs}
        delta = -delta
    if delta < 0:
        return False
    sums = {0}
    for i in range(delta+1):
        if i in sums:
            sums.update(i+d for d in diffs if i+d <= delta)
    return delta in sums


def missing_translation(rules):
    for delta in sorted({r-l for l,r in rules}):
        s, t = max(-delta,0), max(delta,0)
        if not raw(s,t,rules):
            return s,t
    return None


def reduced(word, order):
    """Positive normal form modulo x^d = y^d = 1, before any braid relations."""
    runs = []
    for generator in word:
        if runs and runs[-1][0] == generator:
            _, n = runs.pop()
        else:
            n = 0
        if (n+1) % order:
            runs.append((generator,n+1))
    return tuple(runs)


def cube_contexts(order):
    """Position forward moves giving a reverse modulo finite powers."""
    x, y = (1,), (2,)
    X = x+y+x
    inverse_X = tuple(letter for gen in reversed(X) for letter in (gen,)*(order-1))
    conjugate = X+y+inverse_X
    for i in range(order-1):
        left = x*(order-2-i) + x
        right = inverse_X + conjugate*(i+1) + X
        yield left, right


def cube_return(order):
    X, Y = (1,2,1), (2,1,2)
    current = reduced(Y,order)
    for left,right in cube_contexts(order):
        assert reduced(left+X+right, order) == current
        current = reduced(left+Y+right, order)
    assert current == reduced(X,order)


def check_full_twists():
    checks = 0
    for n in range(2, 6):
        def half_twist(first):
            order = list(range(n))
            reading = []
            pos = first
            while pos is not None:
                order[pos], order[pos+1] = order[pos+1], order[pos]
                reading.append(pos+1)
                pos = next((i for i in range(n-1) if order[i] < order[i+1]), None)
            return tuple(reading)
        delta = half_twist(0)
        full = delta + delta
        complements = {i+1: half_twist(i)[1:] + delta for i in range(n-1)}
        for a,b in product(range(1,n), repeat=2):
            for l,r in [((-a,), (-b,)), ((a,-b), (b,-a))]:
                positive = lambda w: tuple(k for g in w for k in (complements[-g] if g < 0 else (g,)))
                for middle in [(), (a,), (a,b,a)]:
                    assert braid_image(n, positive(l)+middle+positive(r)) == braid_image(n, full*2+l+middle+r)
                    checks += 1
    return checks


def raw_example(emitter):
    ctx, _, sigma = fitted_crossing()
    sigma2 = comp2(ctx,2,sigma,sigma)
    ident = identity(ctx,src(ctx,sigma))
    p,q,base = cube_terms(ctx,v(1),v(1),v(1))
    crossing_ty = infer(ctx,sigma)
    ctx += (arr(base,q,p), arr(crossing_ty,sigma2,sigma))
    emitter.check_type('cube-return',ctx,v(2),arr(base,q,p))
    emitter.check_type('one-sided-rule',ctx,v(3),arr(crossing_ty,sigma2,sigma))
    old_goal = arr(crossing_ty,sigma,ident)
    g = emitter.ctx(ctx)
    emitter.checks.append(f'cancelled-boundary : {g} ⊢ty {emitter.ty(old_goal)}\n'
                          f'cancelled-boundary = from-just (checkTy {g} (from-just (checkCtx {g}))'
                          f' {emitter.ty(old_goal)})\n')


def check():
    count = 0
    small = list(product(range(3),repeat=2))
    for rules in product(small,repeat=2):
        missing = missing_translation(rules)
        exact = True
        for s,t in product(range(4),repeat=2):
            directed, localized = raw(s,t,rules), surface(s,t,rules)
            assert not directed or localized
            if directed != localized:
                exact = False
            count += 1
        # Every minimal test for these inputs lies inside the checked range.
        assert (missing is None) == exact
    for d in range(1,13):
        cube_return(d)
    assert missing_translation([(0,4),(6,0)]) is None
    assert missing_translation([(2,1)]) == (1,0)
    assert missing_translation([(2,4),(4,2)]) is not None
    print(f'{count:,} raw and surface unary comparisons, with 81 whole-width decisions.')
    print(f'{check_full_twists()} signed contexts cleared by positive full twists.')
    print('Constructed contextual forward cube moves for twelve finite crossing orders.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--width-two', nargs='*', metavar='SOURCE:TARGET',
                        help='crossing counts of the declarations at width two')
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.width_two is not None:
        try:
            rules = [tuple(map(int,s.split(':'))) for s in args.width_two]
            if any(len(pair) != 2 or min(pair) < 0 for pair in rules):
                raise ValueError('expected pairs of natural numbers')
        except ValueError as err:
            parser.error(str(err))
        missing = missing_translation(rules)
        if missing:
            print(f'old width-two boundary fails: {missing[0]} -> {missing[1]}')
        elif any(r>l for l,r in rules) and any(r<l for l,r in rules):
            print('all old four-types reflect at every width')
        else:
            print('all old width-two four-types reflect')
        return
    check()
    emitter = Emitter()
    raw_example(emitter)
    if args.agda:
        module = emitter.module(args.agda.stem, 'Fitted scalar crossing and cancelled old boundary.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n', 'open import CaTTExp.Gray.Pure\n'))


if __name__ == '__main__':
    main()
