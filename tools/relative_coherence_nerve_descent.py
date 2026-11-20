"""Check cellular lifts of cyclic bar chains and their integral torsion certificates."""
from argparse import ArgumentParser
from collections import Counter
from itertools import product
from pathlib import Path

from catt import STAR, arr, comp2, infer, maximal_vars, sub_from, subst_tm, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_arity_resolution import difference, linear
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head, string_tree


def bar_faces(m, word):
    yield word[1:]
    for i in range(len(word) - 1):
        yield word[:i] + ((word[i] + word[i+1]) % m,) + word[i+2:]
    yield word[:-1]


def boundary(m, word):
    total = Counter()
    for i, face in enumerate(bar_faces(m, word)):
        total[face] += (-1)**i
    return {key: n for key, n in total.items() if n}


def cellular_lifts(m, emitter):
    ctx = (STAR,)
    def attach(negative, positive):
        nonlocal ctx
        base = infer(ctx, negative)
        assert infer(ctx, positive) == base
        generator = v(len(ctx))
        ctx += (arr(base, negative, positive),)
        return generator

    top = {}
    for a in range(m):
        top[a,] = v(len(ctx))
        ctx += (arr(STAR, v(0), v(0)),)
    def edge(a):
        return top[a % m,]

    chart = tree_ctx(string_tree(0, (1, 1, 1)))
    slots = maximal_vars(chart)
    x, y, z = map(v, slots)
    assoc = head(chart, comp2(chart, 0, comp2(chart, 0, x, y), z),
                 comp2(chart, 0, x, comp2(chart, 0, y, z)))
    for a, b in product(range(m), repeat=2):
        top[a, b] = attach(edge(a+b), comp2(ctx, 0, edge(a), edge(b)))
    for a, b, c in product(range(m), repeat=3):
        labels = (edge(a), edge(b), edge(c))
        transport = subst_tm(assoc, sub_from(chart, ctx, dict(zip(slots, labels, strict=True))))
        negative = comp2(ctx, 1, top[(a+b) % m, c], comp2(ctx, 0, top[a,b], edge(c)))
        negative = comp2(ctx, 1, negative, transport)
        positive = comp2(ctx, 1, top[a, (b+c) % m], comp2(ctx, 0, edge(a), top[b,c]))
        sphere = arr(infer(ctx, edge(a+b+c)), edge(a+b+c),
                     comp2(ctx, 0, edge(a), comp2(ctx, 0, edge(b), edge(c))))
        assert infer(ctx, negative) == infer(ctx, positive) == sphere
        top[a,b,c] = attach(negative, positive)
        if emitter and (a,b,c) == (1,0,1):
            emitter.check_type('negative', ctx, negative, sphere)
            emitter.check_type('positive', ctx, positive, sphere)
            emitter.check_type('tetrahedron', ctx, top[a,b,c], arr(sphere, negative, positive))

    for word, gen in top.items():
        if len(word) < 2:
            continue
        _, _, negative, positive = infer(ctx, gen)
        counted = difference(top_counts(ctx, positive), top_counts(ctx, negative))
        assert counted == {top[face][1]: n for face, n in boundary(m, word).items()}
    return len(top)


def periodic_chain(m, degree):
    return {((1,) if degree % 2 else ()) + tuple(i for a in choices for i in (a,1)): 1
            for choices in product(range(m), repeat=degree//2)}


def torsion_checks(m, pairs):
    def character(word):
        value = word[0]
        for i in range(1, len(word), 2):
            value *= (word[i]+word[i+1]) // m
        return value % m

    checks = 0
    for r in range(pairs):
        odd = 2*r+1
        cycle = periodic_chain(m, odd)
        assert not linear(cycle, lambda word: boundary(m, word))
        assert linear(periodic_chain(m, odd+1), lambda word: boundary(m, word)) == {
            word: m*n for word, n in cycle.items()}
        assert sum(n*character(word) for word, n in cycle.items()) % m == 1
        for word in product(range(m), repeat=odd+1):
            assert sum((-1)**i * character(face) for i, face in enumerate(bar_faces(m, word))) % m == 0
            checks += 1
    return checks


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    for modulus, pairs in ((2, 4), (3, 3), (4, 3), (5, 2)):
        generators = cellular_lifts(modulus, emitter if modulus == 2 else None)
        evaluations = torsion_checks(modulus, pairs)
        print(f'C{modulus}: {generators} typed generators through rank 3; '
              f'order {modulus} in odd bar degrees through {2*pairs-1}; '
              f'{evaluations} cocycle evaluations.')
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Two cyclic bar pastings at the same sphere and their bracket.'))
