"""Check the cap-height restriction for a wedge of two globes."""

from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import product
from pathlib import Path

from catt import disc_tree
from ct_suspension import build
from emit_agda import Emitter
from gray_constant_cylinder import moving_cap_lifts
from gray_globe_exterior_actions import certificate
from gray_globe_comparison import atom, close_atoms, face
from gray_globe_section import trim
from gray_tree_section import generators, tree_boundary
from gray_wedge_cylinders import cut_row


def caps(cell):
    # Row d+1 records the images of the two signed degree-d disk generators.
    result = [[], []]
    for pair in cell[1:]:
        values = [cut_row(Counter(chain), 1)[1] for chain in pair]
        for side in (0, 1):
            result[side].append(tuple(tuple(sorted(v[side].elements())) for v in values))
    return tuple(tuple(cap) for cap in result)


def check(clock, left, right):
    wedge = disc_tree(left) + disc_tree(right)
    basis = product(generators(disc_tree(clock)), generators(wedge))
    atoms = [atom(g, tree_boundary, len) for g in basis]
    cells = close_atoms(atoms, clock + max(left, right))
    counts = Counter()

    @cache
    def intrinsic_caps(cell):
        return tuple(trim(t) for t in caps(cell))

    for padded in cells:
        cell = trim(padded)
        if cell[0][0][0][-1] != ((), 0) or cell[0][1][0][-1] != ((), 2):
            continue
        diagrams = intrinsic_caps(cell)
        height = max(len(t) - 1 for t in diagrams)
        assert height >= 0
        # Independently read the ranks of seam-incident edge generators.
        ranks = [len(k[0]) for pair in cell for chain in pair
                 for k, (address, _) in chain if len(address) == 1]
        assert max(ranks) == height
        if len(cell) > 2:
            for sign in (0, 1):
                boundary_caps = intrinsic_caps(trim(face(cell, sign)))
                expected = tuple(trim(face(t, sign)) for t in caps(cell))
                assert boundary_caps == expected
                assert max(len(t)-1 for t in boundary_caps) <= height
        counts[len(cell)-1, height] += 1
    within = sum(n for (_, h), n in counts.items() if h <= 3)
    moving = sum(n for (_, h), n in counts.items() if h == 3)
    print(f"D^{clock} x (D^{left} wedge D^{right}): {sum(counts.values())} crossings, "
          f"{within} of cap height at most 3, {moving} of cap height exactly 3")
    return counts


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path)
    args = parser.parse_args()
    assert max(h for _, h in check(3, 2, 3)) == 3
    assert max(h for _, h in check(4, 1, 2)) == 4
    lifts = list(moving_cap_lifts(build(3)[3], 6))
    assert [(degree, side) for degree, side, *_ in lifts] == [(5, 0), (5, 1), (6, 0), (6, 1)]
    print("Both moving-cap cylinder types checked in degrees 5 and 6")
    if args.agda:
        emitter = Emitter()
        # Absolute variable levels let the final context contain all four judgments.
        check_type = certificate(emitter, lifts[-1][2])
        for degree, side, _, term, expected in lifts:
            check_type(f"moving-{degree}-{side}", term, expected)
        args.agda.write_text(emitter.module(args.agda.stem, "Moving three-dimensional caps."))
