"""Check the equatorial crossing and both weak unit comparisons in Response 15."""
import argparse
from collections import defaultdict
from itertools import product
from pathlib import Path

from catt import (arr, check_ctx, coh_between, comp2, disc_tree, infer, src,
                  subst_tm, sub_from, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_coloured_faces import visible
from relative_coherence_spherical_fibres import catt_context, ring
from relative_coherence_strip_fibres import Complex, events


def identity(ctx, t):
    from catt import tdim_tm
    tree = disc_tree(tdim_tm(ctx, t))
    top = v(len(tree_ctx(tree)) - 1)
    return coh_between(ctx, tree, [t], top, top)


def crossed_units():
    # Transport a 2-arrow h past a weak identity in each direction.
    disk = tree_ctx(disc_tree(2))
    h = v(len(disk) - 1)
    left = comp2(disk, 1, identity(disk, src(disk, h)), h)
    right = comp2(disk, 1, h, identity(disk, tgt(disk, h)))
    minus = coh_between(disk, disc_tree(2), [h], right, left)
    plus = coh_between(disk, disc_tree(2), [h], left, right)
    wire = tree_ctx(disc_tree(1))
    p = v(len(wire) - 1)
    erase = sub_from(disk, wire, {h[1]: identity(wire, p)})
    minus0, plus0 = (subst_tm(t, erase) for t in (minus, plus))
    doubled = comp2(wire, 1, identity(wire, p), identity(wire, p))
    assert minus0 != plus0
    assert all(infer(wire, t)[2:] == (doubled, doubled) for t in (minus0, plus0))
    comparison = coh_between(wire, disc_tree(1), [p], minus0, plus0)
    assert infer(wire, comparison) == arr(infer(wire, minus0), minus0, plus0)
    return disk, minus, plus, wire, comparison


def check_seam(k, seam):
    base = Complex(*ring(k))
    initial, final, rules, typed = ring(k)
    lane = 2 * seam + 1
    initial, final = list(initial), list(final)
    initial[lane], final[lane] = "tudv", "tveu"

    def decorated_typed(tier):
        # u,v and the two-input crossing marker J all have ports p -> p.
        return typed(tuple(w.translate(str.maketrans("uvJ", "ddd")) for w in tier))

    without = Complex(tuple(initial), tuple(final), rules, decorated_typed)
    assert not without.cells
    rules["J"] = {lane: ("uv", "vu")}
    augmented = Complex(tuple(initial), tuple(final), rules, decorated_typed)
    erase = str.maketrans("", "", "uvJ")
    projected = []
    for cell in augmented.cells:
        steps = {e: j for j, tier in enumerate(cell) for e in events(tier)}
        a, b = chr(65 + 2 * seam), chr(66 + 2 * seam)
        assert steps[a] < steps["J"] < steps[b]
        tiers = [tuple(w.translate(erase) for w in tier) for tier in cell]
        projected.append(base.index[tuple(t for t in tiers if events(t))])
    hidden = {i for i, cell in enumerate(base.cells) if not visible(cell, k)[seam]}
    assert set(projected) == hidden
    assert all(set(base.facets[i]) <= hidden for i in hidden)
    ideals = {i: base.ideal(i) for i in hidden}
    for i, facets in enumerate(augmented.facets):
        assert all(projected[j] in ideals[projected[i]] for j in facets)

    remaining = k - 1
    expected = (1,) + (0,) * (remaining - 2) + (1,) if remaining >= 2 else (2,)
    assert base.betti(hidden) == augmented.betti(set(range(len(augmented.cells)))) == expected
    # Verify all nonempty intersections of the remaining sign sheets, both
    # before and after erasing the crossing. Zero means hidden in that chart.
    signs = {i: visible(base.cells[i], k) for i in hidden}
    for constraints in product((-1, 0, 1), repeat=remaining):
        sheet = {i for i in hidden
                 if all(s == 0 or s == wanted
                        for s, wanted in zip(signs[i][:seam] + signs[i][seam + 1:],
                                              constraints))}
        lifted = {i for i, j in enumerate(projected) if j in sheet}
        assert bool(lifted) == bool(sheet) == any(constraints)
        if sheet:
            assert base.betti(sheet) == augmented.betti(lifted) == (1,)
    print(f"{k} seams, hidden seam {seam + 1}: {len(augmented.cells)} crossing charts,"
          f" {len(hidden)} image charts, mod-two Betti numbers {expected}.")


def six_seam_square():
    base, _, rows = catt_context(6)
    gate = rows[5]["d"]
    p = src(base, gate)
    loop_type = infer(base, gate)
    h, x, y = v(len(base)), v(len(base)), v(len(base) + 1)
    coloured = base + (loop_type,)
    both = base + (loop_type, loop_type)
    swap_type = arr(loop_type, comp2(both, 1, x, y), comp2(both, 1, y, x))
    ctx = both + (swap_type,)
    swap = v(len(both))
    check_ctx(ctx)
    disk, minus, plus, wire, square = crossed_units()
    plug = sub_from(disk, coloured, {len(disk) - 1: h})
    unit = identity(base, p)
    old = tuple(map(v, range(len(base))))
    erased = []
    for ends, head in (((h, unit), minus), ((unit, h), plus)):
        projected = subst_tm(head, plug)
        m = old + ends + (projected,)
        assert infer(coloured, projected)[2:] == tuple(subst_tm(t, m) for t in swap_type[2:])
        erased.append(subst_tm(projected, old + (unit,)))
    comparison = subst_tm(square, sub_from(wire, base, {len(wire) - 1: p}))
    assert infer(base, comparison)[2:] == tuple(erased) and erased[0] != erased[1]
    return ctx, swap


def six_seam_orders():
    # Test every possible hidden set in the actual signal order before and
    # after introducing the crossing. All remaining sign choices share it.
    k = 6
    signal = [(2 * i + 1, 2 * i + 2) for i in range(k - 1)]
    signal += [(2 * k - 1, 2 * k), (2 * k, 0)]

    def acyclic(edges):
        outgoing = defaultdict(set)
        incoming = defaultdict(set)
        for a, b in edges:
            outgoing[a].add(b)
            incoming[b].add(a)
        vertices = set(outgoing) | set(incoming)
        sources = [v for v in vertices if not incoming[v]]
        count = 0
        while sources:
            v = sources.pop()
            count += 1
            for w in outgoing[v]:
                incoming[w].remove(v)
                if not incoming[w]:
                    sources.append(w)
        return count == len(vertices)

    for seam in range(k):
        for bits in product((False, True), repeat=k - 1):
            hidden = list(bits)
            hidden.insert(seam, True)
            cuts = [(2 * i, 2 * i + 1) for i in range(k) if hidden[i] and i != seam]
            a, j, b = 2 * seam, 2 * k + 1, 2 * seam + 1
            assert acyclic(signal + cuts + [(a, b)]) == (not all(hidden))
            assert acyclic(signal + cuts + [(a, j), (j, b)]) == (not all(hidden))
    print("Six seams: the two signal orders agree on all 192 hidden-set tests.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path)
    args = parser.parse_args()
    disk, minus, plus, wire, comparison = crossed_units()
    ctx, swap = six_seam_square()
    six_seam_orders()
    if args.agda:
        emitter = Emitter()
        emitter.check_typed("right-to-left-unit", disk, minus)
        emitter.check_typed("left-to-right-unit", disk, plus)
        emitter.check_typed("seam-erasure-comparison", wire, comparison)
        emitter.check_typed("six-seam-crossing", ctx, swap)
        args.agda.write_text(emitter.module(args.agda.stem, "Unit comparison at a hidden seam."))
    for k in (2, 3):
        for seam in range(k):
            check_seam(k, seam)
