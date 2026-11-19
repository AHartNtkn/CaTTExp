"""Check the fixed frames and the occurrence schedules of Researcher Response 14."""
import argparse
from collections import Counter
from itertools import combinations, product
from pathlib import Path

from catt import (STAR, arr, chain_tree, check_ctx, coh_between, comp2, comp_tree,
                  disc_tree, infer, src, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_antipodal import opposite_term, opposite_type
from relative_coherence_strip_fibres import Complex, events


def reflected_circle():
    rules = {"A": {0: ("l", "r"), 1: ("", "")},
             "B": {1: ("", ""), 2: ("l", "r")}}
    space = Complex(("l", "", "l"), ("r", "", "r"), rules)
    flip = str.maketrans("lr", "rl")
    dual = [space.index[tuple(tuple(w.translate(flip) for w in layer)
                              for layer in reversed(cell))] for cell in space.cells]
    assert space.betti(space.components[0]) == (1, 1)
    fixed = {i for i, j in enumerate(dual) if i == j}
    assert {space.cells[i][0][1] for i in fixed} == {"AB", "BA"}
    assert len(fixed) == 2 and all(space.ideal(i) & fixed == {i} for i in fixed)
    for i, j in enumerate(dual):
        assert dual[j] == i and {dual[k] for k in space.facets[i]} == set(space.facets[j])
    print("Reflected circle: two fixed frames, both serial vertices exchanged.")


def check_schedules():
    # All letters are colours of one loop gate. An address survives every rule.
    # Events C and D need changed letters from A and B respectively, and E
    # subsequently reads a letter from each of C and D.
    replacements = {"A": ("ab", "gh"), "B": ("de", "ij"),
                    "C": ("hc", "kl"), "D": ("ij", "mn"), "E": ("lm", "op")}
    rules = {e: {0: pair} for e, pair in replacements.items()}
    model = Complex(("abcdef",), ("gkopnf",), rules)
    assert len(model.components) == 1
    schedules = {}
    for i, cell in enumerate(model.cells):
        tiers = tuple(events(tier) for tier in cell)
        assert tiers not in schedules
        schedules[tiers] = i

    names = tuple(replacements)
    orders = (("A", "C"), ("B", "D"), ("C", "E"), ("D", "E"))
    independent = set()
    for times in product(range(len(names)), repeat=len(names)):
        slots = set(times)
        if slots != set(range(max(slots) + 1)):
            continue
        time = dict(zip(names, times))
        if all(time[a] < time[b] for a, b in orders):
            independent.add(tuple(frozenset(e for e in names if time[e] == j)
                                  for j in range(len(slots))))
    assert independent == schedules.keys()
    facet_count = 0
    for tiers, i in schedules.items():
        facets = set()
        for j, tier in enumerate(tiers):
            for size in range(1, len(tier)):
                for members in combinations(tier, size):
                    left = frozenset(members)
                    split = tiers[:j] + (left, tier - left) + tiers[j + 1:]
                    facets.add(schedules[split])
        assert facets == set(model.facets[i])
        facet_count += len(facets)
    assert model.betti(model.components[0]) == (1,)
    print("Composite rules:", dict(sorted(Counter(model.degrees).items())),
          "cells by dimension,", facet_count, "facet incidences.")


def fixed_term():
    context = (STAR,)
    dual = [0]

    def arrow(a, b):
        nonlocal context
        ty = infer(context, a)
        assert infer(context, b) == ty
        i = len(context)
        context += (arr(ty, a, b),)
        dual.append(i)
        return v(i)

    f = arrow(v(0), v(0))
    p = arrow(f, f)
    pairs = []
    for _ in range(4):
        minus, plus = arrow(p, p), arrow(p, p)
        dual[minus[1]], dual[plus[1]] = plus[1], minus[1]
        pairs.append((minus, plus))

    def rule(i):
        faces = [comp2(context, 2, pairs[i][side], pairs[i + 1][side]) for side in (0, 1)]
        return arrow(*faces)

    z, y = rule(0), rule(2)
    diagonal = comp2(context, 0, comp2(context, 2, z, y), z)
    # Change the weak source of the diagonal by its left unit comparison.
    globe = tree_ctx(disc_tree(3))
    top = v(len(globe) - 1)
    face = src(globe, top)
    smaller = tree_ctx(disc_tree(2))
    last = v(len(smaller) - 1)
    unit = coh_between(globe, disc_tree(2), [face], last, last)
    padded = comp2(globe, 2, unit, top)
    change = coh_between(context, disc_tree(3), [src(context, diagonal)], padded, top)
    dual = tuple(dual)
    mirrored = opposite_term(change, dual)
    ternary = chain_tree(3)
    for _ in range(3):
        ternary = (ternary,)
    term = comp_tree(ternary, context, [change, diagonal, mirrored])
    check_ctx(context)
    assert all(opposite_type(ty, dual) == context[dual[i]] for i, ty in enumerate(context))
    for candidate in (diagonal, term):
        assert opposite_term(candidate, dual) == candidate
        assert opposite_term(src(context, candidate), dual) == tgt(context, candidate)
    assert src(context, term) != src(context, diagonal)
    print("Raw CaTT: both the nested 4-term and its ternary endpoint correction are fixed.")
    return context, term


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path)
    args = parser.parse_args()
    reflected_circle()
    check_schedules()
    ctx, term = fixed_term()
    if args.agda:
        emitter = Emitter()
        emitter.check_typed("fixed-corrected-diagonal", ctx, term)
        args.agda.write_text(emitter.module(args.agda.stem, "Time-reflected 4-cell with compound faces."))
