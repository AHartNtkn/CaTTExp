"""Find an integral degree potential or a relative cycle modulo an explicit integer."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import chain
import json
from pathlib import Path

from canonical_gray_cube import build_cube
from catt import STAR, arr, comp2, infer, src, subst_tm, tgt, v
from emit_agda import Emitter
from relative_coherence_based_columns import Brackets
from relative_coherence_colour_degree import immutable, relative_columns
from relative_coherence_hidden_seam import identity


def subtract(a, b, q):
    return [x - q*y for x, y in zip(a, b)]


def unit(n, i):
    return [int(i == j) for j in range(n)]


def integral_test(columns, degree):
    """Diagonalize by unimodular moves. Modulus 0 denotes an integral cycle."""
    gens = list(columns)
    faces = sorted(set(chain.from_iterable(columns.values())))
    a = [[columns[g].get(f, 0) for g in gens] for f in faces]
    left = [unit(len(faces), i) for i in range(len(faces))]
    right = [unit(len(gens), i) for i in range(len(gens))]  # columns of R
    d = [degree[g] for g in gens]
    rank = 0

    def swap_rows(i, j):
        a[i], a[j] = a[j], a[i]
        left[i], left[j] = left[j], left[i]

    def swap_cols(i, j):
        for row in a:
            row[i], row[j] = row[j], row[i]
        right[i], right[j] = right[j], right[i]
        d[i], d[j] = d[j], d[i]

    while rank < min(len(faces), len(gens)):
        k = rank
        entry = next(((i, j) for i in range(k, len(faces)) for j in range(k, len(gens))
                      if a[i][j]), None)
        if entry is None:
            break
        swap_rows(k, entry[0])
        swap_cols(k, entry[1])
        while True:
            i = next((i for i in range(k+1, len(faces)) if a[i][k]), None)
            if i is not None:
                q = a[i][k] // a[k][k]
                a[i] = subtract(a[i], a[k], q)
                left[i] = subtract(left[i], left[k], q)
                if a[i][k]:
                    swap_rows(i, k)
                continue
            j = next((j for j in range(k+1, len(gens)) if a[k][j]), None)
            if j is None:
                break
            q = a[k][j] // a[k][k]
            for row in a:
                row[j] -= q*row[k]
            right[j] = subtract(right[j], right[k], q)
            d[j] -= q*d[k]
            if a[k][j]:
                swap_cols(j, k)
        rank += 1

    def obstruction(j, modulus):
        witness = {g: x for g, x in zip(gens, right[j]) if x}
        boundary = Counter()
        volume = 0
        for g, x in witness.items():
            volume += degree[g]*x
            for f, m in columns[g].items():
                boundary[f] += x*m
        if modulus:
            assert all(x % modulus == 0 for x in boundary.values()) and volume % modulus
        else:
            assert not any(boundary.values()) and volume
        return {'modulus': modulus, 'chain': witness, 'degree': volume}

    for j in range(rank, len(gens)):
        if d[j]:
            return obstruction(j, 0)
    coords = []
    for j in range(rank):
        divisor = a[j][j]
        if d[j] % divisor:
            return obstruction(j, abs(divisor))
        coords.append(d[j] // divisor)
    potential = {f: sum(h * row[i] for h, row in zip(coords, left))
                 for i, f in enumerate(faces)}
    assert all(sum(potential[f]*x for f, x in col.items()) == degree[g]
               for g, col in columns.items())
    return {'potential': {f: h for f, h in potential.items() if h}}


def loop_example(repetitions, turns):
    cube, _ = build_cube()
    ctx = cube[:-1]
    u, w = cube[-1][2:]
    f, g = src(ctx, u), tgt(ctx, u)
    back, loop = v(len(ctx)), v(len(ctx)+1)
    ctx += (arr(infer(ctx, g), g, f), arr(infer(ctx, f), f, f))
    def power(t, n):
        result = t
        for _ in range(1, n):
            result = comp2(ctx, 1, result, t)
        return result
    a, b = [power(comp2(ctx, 1, t, back), repetitions) for t in (u, w)]
    b = comp2(ctx, 1, b, power(loop, turns))
    assert infer(ctx, a) == infer(ctx, b)
    ctx += (arr(infer(ctx, a), a, b),)
    colours = [min([3] + [i for i in range(3) if x >> i & 1]) for x in range(8)]
    columns, d = relative_columns(ctx, colours, 3)
    assert columns == {len(ctx)-1: {loop[1]: turns}} and abs(d[len(ctx)-1]) == repetitions
    return ctx, integral_test(columns, d)


def interval_shortcuts(k):
    p = Brackets(k+1)
    @cache
    def extend(vertices):
        if len(vertices) == 2:
            return (p.bracket(*map(v, vertices)),)
        result = set()
        for right in (False, True):
            subset = vertices[:-1] if right else vertices[1:]
            edge, = extend(vertices[-2:] if right else vertices[:2])
            for t in extend(subset):
                u = comp2(p.ctx, 0, t, edge) if right else comp2(p.ctx, 0, edge, t)
                shortcut = p.bracket(src(p.ctx, u), tgt(p.ctx, u))
                result.add(p.bracket(shortcut, u))
        return tuple(sorted(result))
    extend(tuple(range(k+1)))
    columns, d = relative_columns(p.ctx, list(range(k+1)), k)
    return len(columns), integral_test(columns, d)


def based_mod_four(cube, agda):
    p = Brackets(4)
    colours = iter(min([3] + [j for j in range(3) if x >> j & 1]) for x in range(8))
    labels = []
    for ty in cube[:-1]:
        if ty == STAR:
            labels.append(v(next(colours)))
        else:
            labels.append(p.bracket(*(subst_tm(t, labels) for t in ty[2:])))
    a, b = p.base_pair(*(subst_tm(t, labels) for t in cube[-1][2:]), v(0))
    term = b
    for _ in range(3):
        term = comp2(p.ctx, 1, term, a)
    pole = identity(p.ctx, v(0))
    unit = identity(p.ctx, pole)
    assert infer(p.ctx, term) == arr(infer(p.ctx, pole), pole, pole)
    bracket = p.bracket(unit, term)
    columns, d = relative_columns(p.ctx, list(range(4)), 3)
    assert all(x % 4 == 0 for x in columns[bracket[1]].values())
    assert d[bracket[1]] % 4 == 2
    print(f'One based term: full-colour counts {columns[bracket[1]]}, degree {d[bracket[1]]} mod 4.')
    if agda:
        out = Emitter()
        out.check_type('modFourBracket', p.ctx, bracket, arr(infer(p.ctx, unit), unit, term))
        agda.write_text(out.module(agda.stem, 'A based term detecting degree modulo four.'))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, help='same typed-context JSON as the rational solver')
    parser.add_argument('--agda', type=Path, help='emit the four-turn, degree-two example')
    args = parser.parse_args()
    if args.input:
        inp = json.loads(args.input.read_text())
        print(integral_test(*relative_columns(immutable(inp['context']), inp['colours'], inp['degree'])))
        return
    for turns in range(2, 10):
        for r in range(1, turns+1):
            ctx, result = loop_example(r, turns)
            if turns == r:
                assert 'potential' in result
            else:
                assert result['modulus'] == turns and abs(result['degree']) == r
            if (turns, r) == (4, 2):
                based_mod_four(ctx, args.agda)
    print('44 typed loop examples, with modulus 2 through 9 and degree 1 through the modulus.')
    for k in range(3, 7):
        n, result = interval_shortcuts(k)
        assert 'potential' in result
        print(f'Rank {k}: {n} interval shortcuts, integral potential {result["potential"]}.')


if __name__ == '__main__':
    main()
