"""Test which raw Gray cells become equivalences under binary interchange."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import product
from pathlib import Path

from catt import (STAR, arr, comp2, infer, maximal_vars, src, sub_from, subst_tm, tdim,
                  tdim_tm, tgt, v)
from ct_suspension import ident
from emit_agda import Emitter
from semistrict_surface_polygon_heights import raw_prism
from semistrict_surface_scalar_cube import exchange


# Relations on two automaton states: the previous active letter was a
# 2-generator (1), or there was no such previous letter (0).
IDENTITY = frozenset({(0, 0), (1, 1)})
INTERVAL = frozenset({(0, 1)})
HIGHER = frozenset({(0, 0), (1, 0)})


def followed_by(first, second):
    return frozenset((i, k) for i, j in first for l, k in second if j == l)


@cache
def column_tops(arity):
    columns = []
    for i, ty in enumerate(arity[1:], 1):
        if ty == STAR:
            columns.append([])
        else:
            columns[-1].append((tdim(ty) + 1, i))
    result = []
    for column in columns:
        height = max(rank for rank, _ in column)
        result.append((height-1, tuple(i for rank, i in column if rank == height)))
    return tuple(result)


def surface_invertible(ctx, term):
    """The context and term are well typed in the raw Gray kernel."""
    @cache
    def summary(t):
        rank = tdim_tm(ctx, t)
        if rank == 1:
            return IDENTITY  # spatial whisker, including the empty edge path
        if t[0] == 'v':
            return INTERVAL if rank == 2 else HIGHER
        _, arity, _, labels = t
        columns = column_tops(arity)
        if rank != 1 + sum(height for height, _ in columns):
            return frozenset()  # coherence case
        result = IDENTITY
        for _, slots in columns:
            alternatives = frozenset.union(*(summary(labels[i]) for i in slots))
            result = followed_by(result, alternatives)
        return result

    rank = tdim_tm(ctx, term)
    if rank == 0:
        raise ValueError('invertibility requires positive global dimension')
    if rank == 1:
        from relative_coherence_cut import top_counts
        return not top_counts(ctx, term)
    return not any(start == 0 for start, _ in summary(term))


def survives(word, ranks):
    active = [ranks[g] for g in word if ranks[g]]
    return all((i, j) != (1, 1) for i, j in zip(active, active[1:]))


def check_quotient():
    # One edge f, birth a:empty->ff, death b:ff->empty, scalar c.
    # p inserts a followed by b, v is a loop parallel to the scalar square,
    # and q changes that square into the separate declaration v.
    ranks = dict(f=0, a=1, b=1, c=1, p=2, v=2, q=3)
    faces = {'f': {}, 'a': {'ff': 1, '': -1}, 'b': {'': 1, 'ff': -1},
             'c': {}, 'p': {'a': 1, 'b': 1}, 'v': {}, 'q': {'v': 1, 'cc': -1}}

    @cache
    def differential(word):
        out = Counter()
        sign = 1
        for i, g in enumerate(word):
            for face, coefficient in faces[g].items():
                out[word[:i]+face+word[i+1:]] += sign * coefficient
            sign *= (-1)**ranks[g]
        return {w: n for w, n in out.items() if n}

    killed = 0
    for length in range(6):
        for letters in product(ranks, repeat=length):
            word = ''.join(letters)
            twice = Counter()
            signature_boundary = Counter()
            for face, coefficient in differential(word).items():
                for lower, n in differential(face).items():
                    twice[lower] += coefficient*n
                if survives(face, ranks):
                    signature_boundary[tuple(g for g in face if ranks[g])] += coefficient
            assert not any(twice.values())
            if not survives(word, ranks):
                assert not any(signature_boundary.values())
                killed += 1
    return killed


def check_automaton():
    options = ((0,), (1,), (2,), (0, 1), (1, 2))
    count = 0
    for width in range(1, 7):
        for columns in product(options, repeat=width):
            result = IDENTITY
            for column in columns:
                step = frozenset.union(*((IDENTITY, INTERVAL, HIGHER)[i] for i in column))
                result = followed_by(result, step)
            explicit = any(survives(w, range(3)) for w in product(*columns))
            assert explicit == any(i == 0 for i, _ in result)
            count += 1
    return count


def check_bare_squares():
    # Paths on a graph with a loop and two different arrows out of its pole.
    edges = ((0, 0), (0, 1), (0, 1), (1, 2))
    paths = {length: [] for length in range(3)}
    paths[0] = [(x, x, ()) for x in range(3)]
    for length in (1, 2):
        for x, y, w in paths[length-1]:
            for letter, (s, t) in enumerate(edges):
                if y == s:
                    paths[length].append((x, t, w+(letter,)))
    short = sum(paths.values(), [])
    generators = [(x, y, p, q, name) for x, y, p in short for s, t, q in short
                  if (x, y) == (s, t) for name in range(2)]
    same = different = 0
    for a, b in product(generators, repeat=2):
        for x, y, gap in short:
            if (x, y) != (a[1], b[0]):
                continue
            left_first = (((), a, gap+b[2]), (a[3]+gap, b, ()))
            right_first = ((a[2]+gap, b, ()), ((), a, gap+b[3]))
            expected = a == b and not (a[2] or a[3] or gap)
            assert (left_first == right_first) == expected
            if expected:
                same += 1
            else:
                different += 1
    return same, different


def raw_examples():
    out = Emitter()
    out.checks.append("""
rankAt : List Nat → Nat → Nat
rankAt [] _ = 0
rankAt (n ∷ ns) zero = n
rankAt (n ∷ ns) (suc i) = rankAt ns i

hasSquare : List Nat → Bool → Tuple → Bool
hasSquare rs last [] = false
hasSquare rs last (x ∷ xs) with rankAt rs x
... | 0 = hasSquare rs last xs
... | 1 = hasSquare rs last xs
... | 2 = last ∨ hasSquare rs true xs
... | suc (suc (suc n)) = hasSquare rs false xs
""")
    count = 0

    def check(name, ctx, t, predicted):
        nonlocal count
        assert surface_invertible(ctx, t) == predicted, name
        out.check_typed(name, ctx, t)
        ranks = ' ∷ '.join(str(tdim(ty)+1) for ty in ctx) + ' ∷ []'
        out.checks.append(f'{name}-test : all (hasSquare ({ranks}) false) (topS {out.tm(t)})'
                          f' ≡ {str(predicted).lower()}\n{name}-test = refl\n')
        count += 1

    base = (STAR,)
    edge = ident(base, v(0))
    ctx = (*base, arr(infer(base, edge), edge, edge))
    a = v(1)
    square = exchange(ctx, a, a)
    p, q = src(ctx, square), tgt(ctx, square)
    ctx += (arr(infer(ctx, p), p, q), arr(infer(ctx, p), q, p))
    step, back = v(2), v(3)
    round_trip = comp2(ctx, 2, square, back)
    ctx += (arr(infer(ctx, square), square, step),)
    check('scalar-square', ctx, square, True)
    check('parallel-declaration', ctx, step, False)
    check('mixed-round-trip', ctx, round_trip, False)
    check('change-square-to-declaration', ctx, v(4), False)
    check('padded-round-trip', ctx, ident(ctx, round_trip), True)
    for left in (True, False):
        arity, prism, _ = raw_prism(left)
        for label, top, expected in [('square', square, True), ('variable', step, False),
                                     ('mixture', round_trip, False)]:
            inputs = (top, a) if left else (a, top)
            sigma = sub_from(arity, ctx, dict(zip(maximal_vars(arity), inputs, strict=True)))
            check(('left-' if left else 'right-')+label, ctx, subst_tm(prism, sigma), expected)
    return out, count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    print(f'{check_quotient()} killed-word boundaries preserve surviving signatures.')
    print(f'{check_automaton()} column products agree with explicit word expansion.')
    same, different = check_bare_squares()
    print(f'{same} equal and {different} distinct pairs of positioned square histories.')
    emitter, count = raw_examples()
    if args.agda_dir:
        name = 'SurfaceInvertedCells'
        source = emitter.module(name, __doc__).replace('open import CaTTExp.Pure',
                                                       'open import CaTTExp.Gray.Pure')
        (args.agda_dir/(name+'.agda')).write_text(source)
    print(f'{count} raw-cell predictions checked.')
