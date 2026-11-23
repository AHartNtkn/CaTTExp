"""Check the disc-operation obstruction to exact binary rehydration."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, glue_tree, infer, maximal_vars,
                  sub_from, subst_tm, tdim, tdim_tm, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity


def slots(ctx, rank):
    return [i for i, ty in enumerate(ctx) if tdim(ty) + 1 == rank]


@cache
def marks(ctx, term, rank):
    """Keep the entire literal occurrence at each unary top-disc head."""
    if term[0] == 'v':
        return Counter()
    _, arity, _, labels = term
    result = Counter({term: 1}) if arity == tree_ctx(disc_tree(rank)) else Counter()
    for i in slots(arity, rank):
        result.update(marks(ctx, labels[i], rank))
    return result


@cache
def grade(ctx, term, rank):
    if term[0] == 'v':
        return 1
    _, arity, ty, labels = term
    extra = any(marks(arity, face, rank) for face in ty[2:])
    return int(extra) + sum(grade(ctx, labels[i], rank) for i in slots(arity, rank + 1))


def unary(ctx, term):
    rank = tdim_tm(ctx, term)
    arity = tree_ctx(disc_tree(rank))
    top = len(arity) - 1
    return ('coh', arity, arity[top], sub_from(arity, ctx, {top: term}))


def reflexive_pair(point, rank, lower):
    # Clause (ii) on the reflexive word equation w = w, specialized to a point.
    dim = rank - 1
    arity = tree_ctx(glue_tree(dim, dim - 1, dim))
    left, right = maximal_vars(arity)
    word = comp2(arity, dim - 1, v(left), v(right))
    labels = sub_from(arity, point, {left: lower, right: lower})
    return tuple(subst_tm(term, labels) for term in (head(arity, word, word), identity(arity, word)))


def check_pair(point, rank, family, pair, emitter):
    a, b = pair
    assert a != b and infer(point, a) == infer(point, b)
    u, w = unary(point, a), unary(point, b)
    assert infer(point, u) == infer(point, w)
    assert marks(point, u, rank) != marks(point, w, rank)
    for direction, (start, end) in enumerate(((u, w), (w, u))):
        comparison = head(point, start, end)
        assert grade(point, comparison, rank) == 1
        emitter.check_type(f'{family}{rank}dir{direction}', point, comparison,
                           arr(infer(point, start), start, end))
    assert grade(point, identity(point, u), rank) == 0
    # Reassociation around a marked term changes the surrounding syntax
    # while retaining the same literal occurrence. The generic comparison
    # specializes to a zero-grade cell even with the opaque disc input.
    disc = tree_ctx(disc_tree(rank))
    x = v(len(disc) - 1)
    left_unit = comp2(disc, rank - 1, identity(disc, infer(disc, x)[2]), x)
    witness = subst_tm(head(disc, left_unit, x), sub_from(disc, point, {x[1]: u}))
    s, t = infer(point, witness)[2:]
    assert grade(point, witness, rank) == 0 and marks(point, s, rank) == marks(point, t, rank)
    emitter.check_type(f'{family}{rank}outside', point, witness, arr(infer(point, s), s, t))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    point = (STAR,)
    tower = [v(0)]
    for _ in range(4):
        tower.append(identity(point, tower[-1]))
    emitter = Emitter()
    count = 0
    for rank, a in enumerate(tower[1:], 1):
        def top(b, c):
            return comp2(point, rank - 1, b, c)
        pairs = {'assoc': (top(top(a, a), a), top(a, top(a, a))),
                 'unit': (top(a, a), a)}
        if rank >= 2:
            pairs['reflexive'] = reflexive_pair(point, rank, tower[rank - 1])
        for family, pair in pairs.items():
            check_pair(point, rank, family, pair, emitter)
            count += 1
    if args.agda_dir:
        for tag, kernel in [('Ordinary', 'CaTTExp.Pure'), ('Gray', 'CaTTExp.Gray.Pure')]:
            name = tag + 'IdentityClasses'
            source = emitter.module(name, __doc__).replace('open import CaTTExp.Pure', 'open import ' + kernel)
            (args.agda_dir / (name + '.agda')).write_text(source)
    print(f'{count} point pairs in ranks one through four; both directions and all exterior controls checked.')


if __name__ == '__main__':
    main()
