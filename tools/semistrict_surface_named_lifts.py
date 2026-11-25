"""Check independently coloured occurrences of a repeated birth at an empty 2-face."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, subst_ty, tdim_tm, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, string_tree
from relative_coherence_hidden_seam import identity


def build(emitter, base_names=None):
    coloured = base_names is not None
    ctx, names, fold = (), {}, []

    def declare(name, ty):
        nonlocal ctx
        result = v(len(ctx))
        ctx += (ty,)
        if coloured:
            fold.append(base_names[name])
        else:
            assert name not in names
            names[name] = result
        return result

    def arrow(name, s, t):
        assert infer(ctx, s) == infer(ctx, t)
        return declare(name, arr(infer(ctx, s), s, t))

    x = declare('x', STAR)
    if coloured:
        y = declare('x', STAR)
        ll, f, rr = (declare('f', arr(STAR, s, t)) for s, t in ((x, x), (x, y), (y, y)))
        paths = (comp2(ctx, 0, f, rr), comp2(ctx, 0, ll, f))
    else:
        f = ll = rr = declare('f', arr(STAR, x, x))
        paths = (comp2(ctx, 0, f, f),)
    a = arrow('a', f, f)
    unary = (comp2(ctx, 0, a, rr), comp2(ctx, 0, ll, a))
    ports = range(len(paths))
    gates = {(p, q): arrow('H', paths[p], paths[q]) for p, q in product(ports, repeat=2)}
    empty = [identity(ctx, path) for path in paths]
    birth, death = {}, {}
    for p, m in product(ports, repeat=2):
        row = comp2(ctx, 1, gates[p, m], gates[m, p])
        birth[p, m] = arrow('b', empty[p], row)
        death[p, m] = arrow('d', row, empty[p])

    excursions = {}
    for side, probe in enumerate(unary):
        q = side if coloured else 0
        for p in ports:
            first = gates[p, q]
            marked = comp2(ctx, 1, first, probe)
            go = arrow('go' + str(side), first, marked)
            back = arrow('back' + str(side), marked, first)
            for m in ports:
                # The shared 1-pole of the two gates must literally match.
                if tgt(ctx, first) != src(ctx, gates[m, p]):
                    continue
                right = gates[m, p]
                steps = (birth[p, m], comp2(ctx, 1, go, right),
                         comp2(ctx, 1, back, right), death[p, m])
                excursions[p, side, m] = composite(ctx, 2, steps)

    left = unary[0]
    u = arrow('U', left, left)
    up = arrow('V', left, left)
    repair = arrow('repair', u, up)
    row = comp2(ctx, 2, excursions[0, 0, 0], excursions[0, 1, int(coloured)])
    suffix = comp2(ctx, 1, left, row)
    witness = comp2(ctx, 2, comp2(ctx, 1, repair, empty[0]), suffix)
    ends = tuple(comp2(ctx, 2, comp2(ctx, 1, h, empty[0]), suffix) for h in (u, up))
    assert (src(ctx, witness), tgt(ctx, witness)) == ends
    emitter.check_type('coloured' if coloured else 'folded', ctx, witness,
                       arr(infer(ctx, ends[0]), *ends))
    return ctx, names, tuple(fold), witness, set(excursions)


def check(emitter):
    base, names, _, original, _ = build(emitter)
    ctx, _, fold, lifted, events = build(emitter, names)
    for i, ty in enumerate(ctx):
        assert subst_ty(ty, fold[:i]) == infer(base, fold[i])
    assert subst_tm(lifted, fold) == original
    emitter.check_eq('foldAtBothPorts', lifted, fold, original)

    tested = single_choice = 0
    for n in range(6):
        for probes in product(range(2), repeat=n):
            lifts = {choices for choices in product(range(2), repeat=n)
                     if all((0, side, middle) in events for side, middle in zip(probes, choices))}
            assert lifts == {probes}
            fixed = any(all((0, side, m) in events for side in probes) for m in range(2))
            assert fixed == (len(set(probes)) <= 1)
            tested += 1
            single_choice += fixed
    print(f'All {tested} probe words lift at their written ports; {single_choice} admit a fixed birth choice.')


def check_renaming(emitter, rank):
    lower = tree_ctx(disc_tree(rank - 2))
    pole = identity(lower, v(maximal_vars(lower)[0]))
    ty = arr(infer(lower, pole), pole, pole)
    base, named = lower + (ty,), lower + (ty,) * 3
    label = v(len(lower))
    copies = tuple(v(i) for i in range(len(lower), len(named)))
    fold = tuple(map(v, range(len(lower)))) + (label,) * 3

    generic = tree_ctx(string_tree(rank - 1, [rank] * 3))
    tips = maximal_vars(generic)
    a, b, c = map(v, tips)
    left = comp2(generic, rank - 1, comp2(generic, rank - 1, a, b), c)
    right = comp2(generic, rank - 1, a, comp2(generic, rank - 1, b, c))
    comparison = head(generic, left, right)
    upper = sub_from(generic, named, dict(zip(tips, copies, strict=True)))
    old = sub_from(generic, base, {i: label for i in tips})

    def occurrences(ctx, term):
        if tdim_tm(ctx, term) != rank:
            return ()
        if term[0] == 'v':
            return (term,)
        return tuple(z for argument in term[3] for z in occurrences(ctx, argument))

    for side in (left, right):
        assert occurrences(named, subst_tm(side, upper)) == copies
        assert occurrences(base, subst_tm(side, old)) == (label,) * 3
    lifted = subst_tm(comparison, upper)
    original = subst_tm(comparison, old)
    assert subst_tm(lifted, fold) == original
    boundary = arr(infer(named, subst_tm(left, upper)), subst_tm(left, upper), subst_tm(right, upper))
    emitter.check_type('namedRank' + str(rank), named, lifted, boundary)
    emitter.check_eq('foldRank' + str(rank), lifted, fold, original)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    check(emitter)
    for rank in range(2, 6):
        check_renaming(emitter, rank)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('NamedLifts', __doc__).replace('open import CaTTExp.Pure',
                                                               'open import CaTTExp.Gray.Pure')
        (args.agda_dir / 'NamedLifts.agda').write_text(module)
