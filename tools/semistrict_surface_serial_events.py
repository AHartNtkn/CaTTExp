"""Check the temporal product on histories with no reachable spatial exchange."""
from argparse import ArgumentParser
from collections import deque
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import STAR, arr, check_ctx, comp2, comp_tree, infer, tdim, v
from emit_agda import Emitter
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import string_tree
from semistrict_surface_single_event_fibres import PlacedTerms, fixture


def independent(first_left, first_output, next_left, next_input):
    return (first_left + first_output <= next_left
            or next_left + next_input <= first_left)


def fronts():
    n_checked = 0
    for width in range(5):
        for a, b, c in product(range(3), repeat=3):
            # Enumerate every horizontal pair of generator slots on the input
            # row. Read the second placement after the first step.
            exchanges = set()
            for gap in range(width + 1):
                for left in range(width - a - c - gap + 1):
                    exchanges.add((left, left + b + gap))
                    exchanges.add((left + c + gap, left))
            for i in range(width-a+1):
                for j in range(width-a+b-c+1):
                    assert independent(i, b, j, c) == ((i,j) in exchanges)
                    n_checked += 1
    print(f'{n_checked} adjacent-window decisions verified, including empty inputs and outputs')


def placement_products():
    count = 0
    for width in (2, 3, 4):
        for length in (2, 3, 4):
            for spans in product((1, width), repeat=length):
                # A narrow cell can move to any one wire. A spanning cell has
                # one placement. Check the first possible exchange by exploring
                # all private moves, independently of the adjacent-pair test.
                initial = (0,) * length
                seen, queue = {initial}, deque([initial])
                witness = False
                while queue:
                    state = queue.popleft()
                    for i, span in enumerate(spans):
                        for x in (state[i]-1, state[i]+1):
                            if 0 <= x <= width-span:
                                other = state[:i]+(x,)+state[i+1:]
                                if other not in seen:
                                    seen.add(other)
                                    queue.append(other)
                    for i in range(length-1):
                        occupied = [set(range(state[j], state[j]+spans[j])) for j in (i,i+1)]
                        witness |= occupied[0].isdisjoint(occupied[1])
                choices = [range(width-span+1) for span in spans]
                shortcut = any(independent(i, spans[k], j, spans[k+1])
                               for k in range(length-1) for i, j in product(choices[k], choices[k+1]))
                assert seen == set(product(*choices)) and witness == shortcut
                count += 1
    print(f'{count} marked update families checked against explicit placement states')


def coordinates(out):
    ctx, f, a, terms = fixture(False)
    start, end, p, r, loop, update, twice, change, top = terms
    wire = comp2(ctx, 0, f, f)
    d = v(len(ctx))
    ctx += (arr(infer(ctx, wire), wire, wire),)
    u = v(len(ctx))
    ctx += (arr(infer(ctx, d), d, d),)
    check_ctx(ctx)
    read = PlacedTerms(ctx)
    cases = [(start, d, end), (p, u, r), (loop, d, p), (update, u, twice),
             (change, d, update), (top, u, change), (p, d, r, u, loop)]
    for k, factors in enumerate(cases):
        dims = [tdim(infer(ctx, term)) + 1 for term in factors]
        paste = comp_tree(string_tree(1, dims), ctx, factors)
        ty = infer(ctx, paste)
        for i, factor in enumerate(factors):
            term = read.read_event(paste, i)
            height = max(dims)
            if height > 2:
                def frame(ty):
                    if tdim(ty) + 1 == 2:
                        return STAR
                    return arr(frame(ty[1]), read.read_event(ty[2], i), read.read_event(ty[3], i))
                expected = frame(ty)
            else:
                expected = STAR
            assert infer(tuple(read.local), term) == expected
            if height == dims[i]:
                assert top_counts(tuple(read.local), term) == top_counts(tuple(read.local), read.read(factor))
            else:
                assert not top_counts(tuple(read.local), term)
            if out and k in (1,3,5):
                out.check_type(f'row{k}coordinate{i}', tuple(read.local), term, expected)
        if out and k in (1,3,5):
            out.check_type(f'row{k}', ctx, paste, ty)
    check_ctx(tuple(read.local))
    print('All 23 coordinates typechecked on simultaneous updates through degree six')


def rice(binary):
    from semistrict_surface_local_generators import Checker, FULL, WIDTH_ONE
    from semistrict_surface_exact_boundary import rejected
    with TemporaryDirectory() as folder:
        check = Checker(binary.resolve(), Path(folder))
        left, right = 'comp[[a],f]', 'comp[f,[a]]'
        ctx = (f'(x : *) (f : x -> x) (a : f -> f) (d : comp[f,f] -> comp[f,f])'
               f' (p : {left} -> {right}) (r : {right} -> {left}) (A : comp[p,r] -> comp[p,r])')
        flat, nested = 'grouped(A,A,A)', 'h(h(A,A),A)'
        ctx += f' (Z : {flat} -> {flat}) (K : Z -> Z)'
        def placed(t, degree):
            return 'comp[' + '['*(degree-2) + t + ']'*(degree-2) + ',d,' + right + ']'
        fit = 'comp[flat(A,A,A),Z,unflat(A,A,A)]'
        for degree, old, actual, direct, wrong in [
                (5, nested, fit, 'Z', f'id({flat})'),
                (6, fit, 'comp[flat(A,A,A),[K],unflat(A,A,A)]', 'K', 'id(Z)')]:
            boundary = placed(old, degree-1)
            prefix = f'def fitted {ctx} : {boundary} -> {boundary} = '
            for mode in ((), WIDTH_ONE, FULL):
                check.definitions(prefix + placed(actual, degree), mode)
            rejected(check.query(prefix + placed(direct, degree), WIDTH_ONE), 'Check.catt', 'fitted')
            check.equality(placed(actual, degree), placed(direct, degree), ctx, FULL, True)
            check.equality(placed(actual, degree), placed(wrong, degree), ctx, FULL, False)
    print('Rice verified specified classes at two old boundaries on a three-event history')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    parser.add_argument('--rice', type=Path)
    args = parser.parse_args()
    fronts()
    placement_products()
    out = Emitter() if args.agda_dir else None
    coordinates(out)
    if out:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        (args.agda_dir / 'SerialEventProduct.agda').write_text(
            out.module('SerialEventProduct', 'Serial histories with simultaneous higher updates.'))
    if args.rice:
        rice(args.rice)
