"""Compare local judgments with one and two successive single-polygon restrictions."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_exact_boundary import rejected
from semistrict_surface_local_generators import Checker, FULL, WIDTH_ONE


def surround(context, obj, level):
    """Add two parallel polygons, an inaccessible contraction, and a local loop."""
    f, a, b, d, p, r, loose = (name + str(level) for name in ('f', 'a', 'b', 'd', 'p', 'r', 'loose'))
    context += (f' ({f} : {obj} -> {obj}) ({a} : comp[{f},{f}] -> {f})'
                f' ({b} : comp[{f},{f}] -> {f}) ({d} : {f} -> {f})'
                f' (collapse{level} : comp[{a},{d}] -> {a})'
                f' ({p} : {a} -> {b}) ({r} : {b} -> {a})'
                f' ({loose} : comp[{a},id({f})] -> comp[{b},id({f})])')
    return context, a, b, p, r


def fitted_queries(check, context, level):
    if level:
        outward, inward = f'p{level - 1}', f'r{level - 1}'
    else:
        context += ' (y : *) (outward : x -> y) (inward : y -> x)'
        outward, inward = 'outward', 'inward'
    cycle = f'comp[{outward},{inward}]'
    context += f' (step : {cycle} -> {cycle}) (back : {cycle} -> {cycle})'
    # This local edge path visits both polygons. Its three 2-cell updates
    # are horizontally composable because the path returns to its source.
    flat, nested = 'grouped(step,back,step)', 'h(h(step,back),step)'
    context += f' (Z : {flat} -> {flat}) (K : Z -> Z)'
    enter, leave = 'flat(step,back,step)', 'unflat(step,back,step)'
    fitted, higher = f'comp[{enter},Z,{leave}]', f'comp[{enter},[K],{leave}]'
    for mode in ((), WIDTH_ONE, FULL):
        check.definitions(f'def fitted {context} : {nested} -> {nested} = {fitted}\n'
                          f'def higher {context} : {fitted} -> {fitted} = {higher}', mode)
    for name, boundary, var in [('direct', nested, 'Z'), ('upper', fitted, 'K')]:
        code = f'def {name} {context} : {boundary} -> {boundary} = {var}'
        rejected(check.query(code, WIDTH_ONE), 'Check.catt', name)
        check.definitions(code, FULL)
    for term, expected, wrong in [(fitted, 'Z', f'id({flat})'), (higher, 'K', 'id(Z)')]:
        check.equality(term, expected, context, FULL, True)
        check.equality(term, wrong, context, FULL, False)
    print(f'Fitted and distinguished classes in degrees {2 * level + 3} and {2 * level + 4}')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('binary', type=Path)
    args = parser.parse_args()
    with TemporaryDirectory() as temp:
        check = Checker(args.binary.resolve(), Path(temp))
        context, obj = '(x : *)', 'x'
        for level in range(3):
            fitted_queries(check, context, level)
            if level == 2:
                break
            context, obj, b, p, r = surround(context, obj, level)
            for mode in (WIDTH_ONE, FULL):
                check.definitions(f'def padded {context} : {obj} -> {b} = loose{level}\n'
                                  f'def returned {context} : {obj} -> {obj} = comp[{p},{r}]', mode)
                check.equality(f'comp[{p},{r}]', f'id({obj})', context, mode, False)

        context, obj = '(x : *)', 'x'
        for level in range(3):
            scalar_context = context + f' (g : id({obj}) -> id({obj}))'
            square = 'comp[g,g]'
            for mode in (WIDTH_ONE, FULL):
                check.definitions(f'def diagonal {scalar_context} : {square} -> {square} = swap(g,g)', mode)
                check.equality('swap(g,g)', f'id({square})', scalar_context, mode, False)
            f, a = f'f{level}', f'a{level}'
            context += f' ({f} : {obj} -> {obj}) ({a} : comp[{f},{f}] -> {f})'
            obj = a
        print('Diagonal swap and identity distinguished before encoding and at both polygon frames')

        acyclic = ('(x : *) (m : *) (y : *) (f : x -> m) (g : m -> y) (h0 : x -> y)'
                   ' (a0 : comp[f,g] -> h0) (b0 : comp[f,g] -> h0) (p0 : a0 -> b0) (r0 : b0 -> a0)')
        fitted_queries(check, acyclic, 1)
        print('Acyclic polygon presentation verified at both old boundaries')

        base, a, _, _, _ = surround('(x : *)', 'x', 0)
        escaping = base + f' (split : {a} -> comp[{a},d0])'
        vacant = base + ' (vacant : id(f0) -> id(f0))'
        vacant_four = base + ' (higherVacant : id(id(f0)) -> id(id(f0)))'
        for mode in (WIDTH_ONE, FULL):
            four = 'comp[a0,[[higherVacant]]]'
            check.definitions(f'def silentSide {vacant_four} : id(a0) -> id(a0) = {four}', mode)
            check.equality(four, 'id(id(a0))', vacant_four, mode, False)
            for ctx, term in [(escaping, 'comp[split,collapse0]'), (vacant, 'comp[a0,[vacant]]')]:
                check.definitions(f'def excursion {ctx} : a0 -> a0 = {term}', mode)
                check.equality(term, 'id(a0)', ctx, mode, False)
        print('Both a two-event excursion and stationary-side updates in two degrees survive at bare endpoints')


if __name__ == '__main__':
    main()
