"""Verify the top-rule dependency calculation and relative positive-cut hom example."""
from argparse import ArgumentParser
from functools import cache
from itertools import combinations
from pathlib import Path

from catt import arr, comp2, fv_tm, infer, src, subst_tm, tgt, v
from ct_suspension import ident
from relative_coherence_exchange_faces import composite
from semistrict_surface_directed_power_queries import crossing
from semistrict_surface_inverse_completion import DerivationEmitter
from semistrict_surface_positional_tags import loop_tower
from semistrict_surface_top_string_tester import check_map


def expansion_block(rules):
    obstructed = {r for r in rules if len(r[0]) != 1}
    while True:
        produced = {name for _, rhs in obstructed for name in rhs}
        new = {r for r in rules - obstructed if r[0][0] in produced}
        if not new:
            return rules - obstructed
        obstructed.update(new)


def contraction_block(rules):
    return {(r, l) for l, r in expansion_block({(r, l) for l, r in rules})}


def check_blocks():
    # On these word presentations, a one-letter side denotes a literal variable.
    pool = [('ab', 'bc'), ('aa', 'b'), ('a', 'bb'), ('a', 'a'), ('b', 'a'),
            ('b', 'cc'), ('cc', 'c'), ('c', 'ba'), ('', 'a'), ('c', '')]

    @cache
    def terminal(rules):
        answers = set()
        seq = sorted(rules)
        for size in range(1, len(seq) + 1):
            for candidate in combinations(seq, size):
                block = frozenset(candidate)
                rest = rules - block
                exp = all(len(l) == 1 and all(l not in r0 for _, r0 in rest) for l, _ in block)
                con = all(len(r) == 1 and all(r not in l0 for l0, _ in rest) for _, r in block)
                if exp or con:
                    answers.update(terminal(rest))
        return answers or {rules}

    for size in range(len(pool) + 1):
        for selected in combinations(pool, size):
            rules = frozenset(selected)
            core = rules
            while True:
                new = core - expansion_block(core) - contraction_block(core)
                if new == core:
                    break
                core = new
            assert terminal(rules) == {core}
    return 2 ** len(pool)


def check_relative_comparison(emitter):
    # base has a genuine 4-rule between compounds; its 4-event survives collapse.
    base = loop_tower(2)
    pole = comp2(base, 1, v(2), v(2))
    ty = arr(infer(base, pole), pole, pole)
    a, b, c = [v(len(base) + i) for i in range(3)]
    base += (ty,) * 3
    ab, bc = comp2(base, 2, a, b), comp2(base, 2, b, c)
    retained = v(len(base))
    base += (arr(ty, ab, bc),)
    source = v(len(base))
    upper = base + (ty,)
    outgoing = v(len(upper))
    upper += (arr(ty, source, ab),)
    collapse = tuple(map(v, range(len(base)))) + (ab, ident(base, ab))
    check_map(upper, base, collapse)
    varied = composite(upper, 3, (outgoing, retained))
    # Both 4-intervals use the base rule. The final 3-ends have only old names.
    original = crossing(upper, varied, retained)
    projected = subst_tm(original, collapse)
    base_varied = comp2(base, 3, ident(base, ab), retained)
    expected = crossing(base, base_varied, retained)
    assert expected == projected
    assert outgoing[1] in fv_tm(original) and retained[1] in fv_tm(projected)
    assert src(base, projected) != tgt(base, projected)
    for side in (src, tgt):
        assert subst_tm(side(upper, original), collapse) == side(base, expected)
    if emitter is not None:
        emitter.check_type('relativeSquare', upper, original, infer(upper, original))
        emitter.check_type('collapsedAtBothFaces', base, projected, infer(base, expected))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    count = check_blocks()
    emitter = DerivationEmitter() if args.agda_dir else None
    check_relative_comparison(emitter)
    if emitter is not None:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        (args.agda_dir / 'RelativeTopRules.agda').write_text(
            emitter.module('RelativeTopRules', __doc__).replace(
                'open import CaTTExp.Pure\n', 'open import CaTTExp.Pure\n'
                'open import CaTTExp.PastingCheck ∅ using () renaming (checkPs to pastable)\n'))
    print(f'Checked all elimination orders on {count} presentations and both faces of the relative square.')


if __name__ == '__main__':
    main()
