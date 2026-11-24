"""Check coherent binary names below a higher declaration comparing two histories."""
from argparse import ArgumentParser
from itertools import combinations, combinations_with_replacement, product
from math import gcd
from pathlib import Path

from catt import (arr, check_ctx, comp2, disc_tree, infer, maximal_vars, src,
                  sub_from, subst_tm, subst_ty, tdim_tm, tgt, tree_ctx, v)
from ct_suspension import susp_ctx
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_hidden_seam import identity
from relative_coherence_hurewicz_three import determinant
from semistrict_surface_first_failure_gate import attach_copy
from semistrict_surface_odd_cubes import walking_piece


def ports(context, term, rank):
    if tdim_tm(context, term) < rank:
        return
    if term[0] == 'v':
        yield term[1]
    else:
        for arg in term[3]:
            yield from ports(context, arg, rank)


def walking_name(context, fold, seed, depth):
    """Instantiate the walk and its fold from the same generic disc."""
    rank = tdim_tm(context, seed)
    walk = walking_piece(depth)
    for _ in range(rank):
        walk = susp_ctx(walk)
    disc = tree_ctx(disc_tree(rank))
    end = len(disc) - 1
    assert walk[:end + 1] == disc
    sigma = sub_from(disc, context, {end: seed})
    returned_seed = subst_tm(seed, fold)
    seed_at_old = tuple(subst_tm(t, fold) for t in sigma)
    generic_fold = tuple(v(i) for i in range(len(disc)))
    start = len(context)
    for i, ty in enumerate(walk[end + 1:]):
        local_type = subst_ty(ty, sigma)
        context += (local_type,)
        sigma += (v(start + i),)
        collapsed = subst_ty(ty, generic_fold)
        if i == 0:
            value = v(end)
        elif i <= 3:
            value = identity(disc, v(end))
        else:
            value = head(disc, collapsed[2], collapsed[3])
        assert infer(disc, value) == collapsed
        generic_fold += (value,)
        fold += (subst_tm(value, seed_at_old),)
    assert fold[start] == returned_seed
    # At the first two levels the walk has a forward gate, left and right
    # inverses, then the cancellation of forward followed by right inverse.
    return context, fold, v(start), v(start + 1), v(start + 3), v(start + 4)


def check_rank(em, r):
    n = r - 1
    # A single r-1 dimensional loop used three times in a binary expression.
    base = tree_ctx(disc_tree(n - 1))
    pole = v(len(base) - 1)
    loop_type = arr(infer(base, pole), pole, pole)
    a = v(len(base))
    base += (loop_type,)
    pair = comp2(base, n - 1, a, a)
    triple = comp2(base, n - 1, pair, a)
    ztype = arr(infer(base, triple), triple, triple)
    old = base + (ztype, ztype, ztype)
    z, y, w = (v(i) for i in range(len(base), len(old)))
    old_left, old_right = comp2(old, n, z, w), comp2(old, n, y, w)
    upper = arr(infer(old, old_left), old_left, old_right)
    rho = v(len(old))
    old += (upper,)
    new = base
    fold = tuple(v(i) for i in range(len(base)))
    new, fold, short, p, pinv, cancel = walking_name(new, fold, pair, 2)
    named_triple = comp2(new, n - 1, short, a)
    new, fold, full, q, qinv, _ = walking_name(new, fold, named_triple, 2)
    central_type = arr(infer(new, full), full, full)
    names = [v(len(new) + i) for i in range(3)]
    new += (central_type,) * 3
    fold += (z, y, w)
    enter = comp2(new, n, comp2(new, n - 1, p, a), q)
    leave = comp2(new, n, qinv, comp2(new, n - 1, pinv, a))

    def wrap(ctx, left, cell, right):
        return comp2(ctx, n, comp2(ctx, n, left, cell), right)

    programs = [wrap(new, enter, cell, leave) for cell in names]
    translation = tuple(v(i) for i in range(len(base))) + tuple(programs)
    new_upper = subst_ty(upper, translation)
    new_rho = v(len(new))
    new += (new_upper,)
    em.check_type(f'translated{r}', new, new_rho, new_upper)
    round_trip = comp2(new, n, p, pinv)
    cancellation_type = arr(infer(new, round_trip), round_trip, identity(new, pair))
    assert infer(new, cancel) == cancellation_type
    em.check_type(f'cancel{r}', new, cancel, cancellation_type)
    # The actual folded entrance/exit on a generic three-letter word.
    chart = tree_ctx(string_tree(n - 1, [n] * 3))
    a0, a1, a2 = [v(i) for i in maximal_vars(chart)]
    ab = comp2(chart, n - 1, a0, a1)
    abc = comp2(chart, n - 1, ab, a2)
    first = comp2(chart, n - 1, identity(chart, ab), a2)
    one = identity(chart, abc)
    entered, exited = comp2(chart, n, first, one), comp2(chart, n, one, first)
    specialize = sub_from(chart, old, {i: a for i in maximal_vars(chart)})

    def on_word(x, y):
        return subst_tm(head(chart, x, y), specialize)

    disc = tree_ctx(disc_tree(r))
    cell = v(len(disc) - 1)
    padded = wrap(disc, identity(disc, src(disc, cell)), cell, identity(disc, tgt(disc, cell)))

    def compare(zval, reverse):
        incoming, outgoing = (entered, one), (exited, one)
        if reverse:
            incoming, outgoing = (one, entered), (one, exited)
        # Two lifted changes have the literal end faces of the wrapped r-cell.
        inner = comp2(old, n, on_word(*incoming), zval)
        move = comp2(old, n, inner, on_word(*outgoing))
        ends = (cell, padded) if reverse else (padded, cell)
        unit = subst_tm(head(disc, *ends), sub_from(disc, old, {cell[1]: zval}))
        return comp2(old, r, unit, move) if reverse else comp2(old, r, move, unit)

    into = comp2(old, n, compare(z, False), compare(w, False))
    out = comp2(old, n, compare(y, True), compare(w, True))
    transported = comp2(old, r, comp2(old, r, into, rho), out)
    assert infer(old, transported) == subst_ty(new_upper, fold)
    em.check_type(f'returned{r}', old, transported, subst_ty(new_upper, fold))
    # Every auxiliary declaration has a raw image at its substituted type.
    fold += (transported,)
    profiles = []
    for i, ty in enumerate(new):
        assert infer(old, fold[i]) == subst_ty(ty, fold[:i])
        if tdim_tm(new, v(i)) == r:
            profiles.append(tuple(len(tuple(ports(new, face, n))) for face in ty[2:]))
    # Two binary naming steps, each with two reverse gates, and three
    # central declarations between variables.
    assert sorted(profiles) == sorted([(2, 1)] * 2 + [(1, 2)] * 4 + [(1, 1)] * 3)
    check_ctx(new)
    return len(new) - len(base)


def separate_at(context, rank, cap):
    result, images = (), ()
    for index, ty in enumerate(context):
        rewritten = subst_ty(ty, images)
        if tdim_tm(context, v(index)) != rank:
            images += (v(len(result)),)
            result += (rewritten,)
            continue
        source, target = rewritten[2:]
        result, entrance_name = attach_copy(result, source, cap)
        result, exit_name = attach_copy(result, target, cap)
        centre = v(len(result))
        result += (arr(rewritten[1], entrance_name, exit_name),)
        entrance, exit_gate = v(entrance_name[1] + 1), v(exit_name[1] + 3)
        program = comp2(result, rank - 1, comp2(result, rank - 1, entrance, centre), exit_gate)
        assert infer(result, program) == rewritten
        images += (program,)
    return result, images


def check_descending(em):
    point = tree_ctx(disc_tree(0))
    unit = identity(point, v(0))
    scalar = v(len(point))
    base = point + (arr(infer(point, unit), unit, unit),)
    pair = comp2(base, 1, scalar, scalar)
    query = arr(infer(base, pair), pair, pair)
    original = base + (query,)
    first, high = separate_at(original, 3, 3)
    result, low = separate_at(first, 2, 3)
    images = tuple(subst_tm(term, low) for term in high)
    em.check_type('descending', result, images[-1], subst_ty(query, images))
    checked = 0
    for index, ty in enumerate(result):
        rank = tdim_tm(result, v(index))
        if rank >= 2:
            left, right = (set(ports(result, face, rank - 1)) for face in ty[2:])
            assert not left.intersection(right) and (left or right)
            checked += 1
    return checked


def torsion_factors(columns):
    # Determinantal divisors for the cokernel of a three-by-three matrix.
    first = gcd(*(value for column in columns for value in column))
    second = gcd(*(a[i] * b[j] - a[j] * b[i] for a, b in combinations(columns, 2)
                   for i, j in combinations(range(3), 2)))
    divisors = [1, first, second, abs(determinant(*columns))]
    return [b // a for a, b in zip(divisors, divisors[1:]) if b]


def check_two_ports():
    # Columns differing by an overall sign give the same relation.
    columns = {max(col, tuple(-x for x in col))
               for col in product(range(-2, 3), repeat=3) if sum(map(abs, col)) <= 2}
    checks = 0
    for matrix in combinations_with_replacement(sorted(columns), 3):
        assert all(value in (1, 2) for value in torsion_factors(matrix))
        checks += 1
    # Binary naming of three copies of a, followed by a death.
    assert torsion_factors([(-2, 1, 0), (-1, -1, 1), (0, 0, -1)]) == [1, 1, 3]
    return checks


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    for rank in (2, 3, 4):
        print(f'Rank {rank}: {check_rank(emitter, rank)} declarations above the base checked')
    print(f'Descending compilation: {check_descending(emitter)} disjoint face pairs')
    print(f'Two-port relation matrices: {check_two_ports()}')
    if args.agda_dir:
        for prefix, kernel in [('Ordinary', 'CaTTExp.Pure'), ('Gray', 'CaTTExp.Gray.Pure')]:
            name = prefix + 'InteriorPorts'
            module = emitter.module(name, __doc__).replace('open import CaTTExp.Pure\n',
                                                           f'open import {kernel}\n')
            (args.agda_dir / (name + '.agda')).write_text(module)
