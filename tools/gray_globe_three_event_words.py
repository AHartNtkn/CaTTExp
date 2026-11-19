"""Check the coherent sorting of cut-two words of globe-pair 3-cells."""
import argparse
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path

from catt import (arr, comp2, disc_tree, glue_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, subst_ty, tgt, tree_ctx, v)
from emit_agda import Emitter
from gray_globe_attachments import ordered_factors
from gray_globe_comparison import atom, boundary, strict_cells
from gray_globe_factorizations import components, orders, profile, rank


def swapped(word, i):
    return word[:i] + (word[i+1], word[i]) + word[i+2:]


def check_words():
    level = strict_cells((4, 4), 3)
    counts = Counter()
    for cell in level:
        events = cell[3][0]
        if not events:
            continue
        precedences = orders(cell, 2, {rank(g): g for g in events})
        words = {w for w in permutations(events)
                 if all(w.index(a) < w.index(b) for a, b in precedences)}
        reference = min(words)
        counts['cells'] += 1
        counts['words'] += len(words)
        for w in words:
            state = Counter(cell[2][0])
            for g in w:
                before = tuple(sorted(state.elements()))
                state.update(boundary(g))
                assert all(n >= 0 for n in state.values())
                after = tuple(sorted(state.elements()))
                assert cell[:2] + ((before, after), ((g,), (g,))) in level
            assert tuple(sorted(state.elements())) == cell[2][1]
            descents = [i for i in range(len(w)-1)
                        if reference.index(w[i]) > reference.index(w[i+1]) and swapped(w, i) in words]
            assert bool(descents) == (w != reference)
            for i, j in combinations(descents, 2):
                assert j-i > 1
                other = swapped(swapped(w, i), j)
                assert other == swapped(swapped(w, j), i) and other in words
                counts['disjoint diamonds'] += 1
    print(dict(counts))


def central_whiskerings():
    counts = Counter()
    for w in strict_cells((4, 4), 4):
        if len(w[4][0]) != 1 or rank(w[4][0][0]) != (2, 2):
            continue
        # At cut two the central component joins (1,2) to (2,1).
        owner = {p: -1 if p == (0, 3) else 1 if p == (3, 0) else 0
                 for p in profile(w) if sum(p) > 2}
        edges = orders(w, 2, owner)
        central = atom(w[4][0][0])
        groups = set(owner.values())
        legal = [word for word in permutations(groups)
                 if all(word.index(a) < word.index(b) for a, b in edges)]
        for word in legal:
            priority = {p: word.index(g) for p, g in owner.items()}
            operands = ordered_factors(w, 2, priority)
            assert operands[word.index(0)] == central
            for side in (0, 1):
                run = []
                for t in operands:
                    sites = t[3][side]
                    prec = orders(t[:3] + ((sites, sites),), 2, {rank(g): g for g in sites})
                    inside, = (v for v in permutations(sites)
                               if all(v.index(a) < v.index(b) for a, b in prec))
                    run.extend(inside)
                face = w[:3] + ((w[3][side], w[3][side]),)
                prec = orders(face, 2, {rank(g): g for g in run})
                assert set(run) == set(w[3][side])
                assert all(run.index(a) < run.index(b) for a, b in prec)
        if len(legal) == 2:
            assert legal[0].index(0) == legal[1].index(0) and legal[0].index(0) != 1
        else:
            assert len(legal) == 1
        counts[len(legal)] += 1
    print('Single (2,2) steps by number of legal whiskering orders:', dict(sorted(counts.items())))


def disjoint_exchange(emitter):
    ctx = tree_ctx(glue_tree(4, 2, 4))
    a, b = map(v, maximal_vars(ctx))
    top = comp2(ctx, 3, comp2(ctx, 2, a, src(ctx, b)), comp2(ctx, 2, tgt(ctx, a), b))
    bottom = comp2(ctx, 3, comp2(ctx, 2, src(ctx, a), b), comp2(ctx, 2, a, tgt(ctx, b)))
    assert top != bottom and infer(ctx, top) == infer(ctx, bottom)
    results = []
    for label, x, y in (('forward', top, bottom), ('backward', bottom, top)):
        wanted = arr(infer(ctx, x), x, y)
        witness = ('coh', ctx, wanted, tuple(map(v, range(len(ctx)))))
        assert infer(ctx, witness) == wanted
        results.append(witness)
        if emitter:
            emitter.check_type(label, ctx, witness, wanted)
    print('Both generic 5-comparisons typecheck over the two 4-globes glued at cut two')
    return results[0]


def exterior_exchange(ctx, chosen, exterior):
    """Exchange the two actual pure steps on their common cut-one presentation."""
    groups = components(profile(exterior), 1)
    pieces = ordered_factors(exterior, 1, {p: i for i, group in enumerate(groups) for p in group})
    dims = [len(c)-1 for c in pieces]
    arity = tree_ctx((tuple(disc_tree(d-2) for d in dims),))
    slots = maximal_vars(arity)
    active = [i for i, d in enumerate(dims) if d == 3]
    assert len(active) == 2

    def order(events):
        done = set()
        steps = []
        for event in events:
            args = list(map(v, slots))
            for i in active:
                if i != event:
                    endpoint = tgt if i in done else src
                    args[i] = endpoint(arity, args[i])
            t = args[0]
            for arg in args[1:]:
                t = comp2(arity, 1, t, arg)
            steps.append(t)
            done.add(event)
        return comp2(arity, 2, *steps)

    left, right = order(active), order(reversed(active))
    assert infer(arity, left) == infer(arity, right)
    ty = arr(infer(arity, left), left, right)
    sigma = sub_from(arity, ctx, {s: chosen[c] for s, c in zip(slots, pieces)})
    return ('coh', arity, ty, sigma)


def instantiated_exchanges(generic, emitter):
    from canonical_gray_two_discs import strict_interpreter
    from gray_globe_pure_extension import extend, two_by_two
    from gray_globe_sector_terms import boundary_bridge

    left = extend(two_by_two(), (2, 2), 0, 3, None)
    ctx, names, chosen = extend(left, (3, 2), 1, 3, None)
    evaluate = strict_interpreter(ctx, tuple(names))
    seen = set()
    for w in chosen:
        if len(w) != 5 or len(w[4][0]) != 1 or rank(w[4][0][0]) != (2, 2):
            continue
        middle = {(2, 2), (2, 1), (1, 2)}
        owner = {p: int(p in middle) for p in profile(w) if sum(p) > 2}
        if not {(0, 3), (3, 0)} <= owner.keys():
            continue
        # Both exterior changes must be on the same side of the central atom.
        side_edges = orders(w, 2, owner)
        if len(side_edges) != 1:
            continue
        (before, _), = side_edges
        first = before == 1
        if first in seen:
            continue
        pieces = ordered_factors(w, 2, owner)
        center, exterior = pieces if first else pieces[::-1]
        move = names[w[4][0][0]]
        assert evaluate(move) == center
        switch = exterior_exchange(ctx, chosen, exterior)
        assert evaluate(switch) == exterior + (((), ()),)
        # Match the literal 2-seam of the central variable before substitution.
        lo, hi = (tgt(ctx, tgt(ctx, move)), src(ctx, src(ctx, switch))) if first else (
            tgt(ctx, tgt(ctx, switch)), src(ctx, src(ctx, move)))
        if lo != hi:
            bridge = boundary_bridge(ctx, evaluate, names, lo, hi)
            switch = comp2(ctx, 2, bridge, switch) if first else comp2(ctx, 2, switch, bridge)
        args = (move, switch) if first else (switch, move)
        arity = generic[1]
        sigma = sub_from(arity, ctx, dict(zip(maximal_vars(arity), args)))
        term = subst_tm(generic, sigma)
        wanted = subst_ty(generic[2], sigma)
        assert infer(ctx, term) == wanted
        assert wanted[2] != wanted[3]
        assert evaluate(wanted[2]) == evaluate(wanted[3]) == w
        assert evaluate(term) == w + (((), ()),)
        if emitter:
            emitter.check_type('center-first' if first else 'center-last', ctx, term, wanted)
        seen.add(first)
    assert seen == {False, True}
    print('Checked both middle-generator placements with actual pure 3-events and strict identity 5-image')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    check_words()
    central_whiskerings()
    emitter = Emitter() if args.agda else None
    generic = disjoint_exchange(emitter)
    instantiated_exchanges(generic, emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Disjoint exchanges of 3-events.'))
