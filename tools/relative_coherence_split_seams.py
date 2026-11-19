"""Check two-wire seam placements and their effect on the one-bridge ring."""
import argparse
from itertools import product
from pathlib import Path

from catt import (STAR, arr, check_ctx, coh_between, comp2, disc_tree, glue_tree,
                  infer, maximal_vars, src, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_spherical_fibres import ring
from relative_coherence_strip_fibres import Complex, events


def sign_options(before, after):
    if before < after:
        return {"+"}
    if before > after:
        return {"-"}
    return {"+", "-"}


def local_graph(n, m):
    # Occurrence names A and B denote the deletion and insertion.
    model = Complex(("d" * n, "e" * m), ("d" * (n - 1), "e" * (m + 1)),
                    {"A": {0: ("d", ""), 1: ("", "")},
                     "B": {0: ("", ""), 1: ("", "e")}})
    classified = set()
    for i, j, k, ell in product(range(n), range(n), range(m + 1), range(m + 1)):
        def mark(letter, size, gap, marker):
            return letter * gap + marker + letter * (size - gap)

        hidden = ((mark("d", n - 1, i, "A"), mark("e", m, k, "A")),
                  (mark("d", n - 1, j, "B"), mark("e", m, ell, "B")))
        centre = model.index[hidden]
        component = next(c for c in model.components if centre in c)
        left, right = sign_options(i, j), sign_options(k, ell)
        assert len(component) == 1 + 2 * len(left & right)
        for index in component - {centre}:
            cell = model.cells[index]
            if len(cell) == 1:
                orders = {w.index("A") < w.index("B") for w in cell[0]}
                assert len(orders) == 1
                assert centre in model.facets[index]
        assert not component & classified
        classified.update(component)
        for lsign, rsign in product(left, right):
            # In the B-first history count the still present d on the left
            # and the already inserted e on the right when reading the gaps.
            visible = ((mark("d", n, j + (lsign == "+"), "B"), mark("e", m, ell, "B")),
                       (mark("d", n - 1, i, "A"), mark("e", m + 1, k + (rsign == "-"), "A")))
            vertex = model.index[visible]
            if lsign == rsign:
                assert vertex in component
            else:
                assert {vertex} in model.components and vertex not in classified
                classified.add(vertex)
    assert classified == set(range(len(model.cells)))
    return len(classified)


def split_ring(k, seam, repeated):
    old_start, old_end, rules, typed = ring(k)
    lane = 2 * seam + 1
    a, b = chr(65 + 2 * seam), chr(66 + 2 * seam)
    start = old_start[:lane] + (("tdd", "te") if repeated else ("td", "t")) + old_start[lane + 1:]
    end = old_end[:lane] + (("td", "tee") if repeated else ("t", "te")) + old_end[lane + 1:]
    split = {}
    for e, ports in rules.items():
        new = {i + (i > lane): pair for i, pair in ports.items() if i != lane}
        if lane in ports:
            new[lane] = ports[lane] if e == a else ("", "")
            new[lane + 1] = ports[lane] if e == b else ("", "")
        split[e] = new

    def both_typed(tier):
        return all(typed(tier[:lane] + (word,) + tier[lane + 2:]) for word in tier[lane:lane + 2])

    return Complex(start, end, split, both_typed)


def ring_label(k, seam, repeated):
    model = split_ring(k, seam, repeated)
    a, b = chr(65 + 2 * seam), chr(66 + 2 * seam)
    lane = 2 * seam + 1
    selected = set()
    for i, cell in enumerate(model.cells):
        times = {e: t for t, tier in enumerate(cell) for e in events(tier)}
        at, bt = times[a], times[b]
        if repeated:
            # x precedes A on the left, A precedes y on the right.
            # B precedes x on the left, y precedes B on the right.
            if at >= bt:
                continue
            # The bridge can share a tier but reads only before the prefixes.
            placements = tuple(tuple(w.replace("Z", "") for w in cell[t][lane:lane + 2])
                               for t in (at, bt))
            if placements != (("td" + a, "t" + a + "e"), ("t" + b + "d", "te" + b)):
                continue
        elif bt < at:
            # In this history A's future d is still present at B and B's
            # past e is still present at A. The two spatial signs must agree.
            left, right = cell[bt][lane], cell[at][lane + 1]
            if (left.index("d") < left.index(b)) != (right.index(a) < right.index("e")):
                continue
        selected.add(i)
    r = k - int(repeated)
    parts = [c for c in model.components if c <= selected]
    assert set.union(*parts) == selected
    if r == 1:
        assert len(parts) == 2 and all(model.betti(c) == (1,) for c in parts)
    else:
        assert len(parts) == 1
        assert model.betti(selected) == (1,) + (0,) * (r - 2) + (1,)
    # Compare the entire complex to the unsplit ring, or its hidden-seam
    # subcomplex. Forget only the two specified surviving occurrences.
    def erase_tags(tier):
        left, right = tier[lane:lane + 2]
        return tier[:lane] + (left.replace("d", "", 1), right.replace("e", "", 1)) + tier[lane + 2:]

    split_index = {}
    for i in selected:
        cell = model.cells[i]
        key = tuple(map(erase_tags, cell)) if repeated else cell
        assert key not in split_index
        split_index[key] = i
    original = Complex(*ring(k))
    correspondence = {}
    for j, cell in enumerate(original.cells):
        times = {e: t for t, tier in enumerate(cell) for e in events(tier)}
        if repeated and times[a] >= times[b]:
            continue
        image = tuple(t[:lane] + (t[lane].replace("e", ""), t[lane].replace("d", "")) +
                      t[lane + 1:] for t in cell)
        correspondence[j] = split_index[image]
    assert len(correspondence) == len(selected) and set(correspondence.values()) == selected
    for j, i in correspondence.items():
        assert {correspondence[f] for f in original.facets[j]} == set(model.facets[i])
    print(f"{k} seams, split {seam + 1}, repeated={repeated}:",
          len(selected), "charts,", len(parts), "strict label(s), Betti", model.betti(selected))


def six_seam_terms():
    # Keep ordinary signal lanes intact. At the third seam d lives only
    # on the first wire and e only on the second.
    k, seam = 6, 2
    _, _, ordinary_rules, _ = ring(k)
    widths = [1 + (i == 2 * seam + 1) for i in range(2 * k + 1)]
    objects = tuple(v(i) for i in range(sum(widths) + 1))
    ctx = (STAR,) * len(objects)

    def arrow(a, b):
        nonlocal ctx
        ty = infer(ctx, a)
        assert ty == infer(ctx, b)
        u = v(len(ctx))
        ctx += (arr(ty, a, b),)
        return u

    def identity(wire):
        p = v(len(tree_ctx(disc_tree(1))) - 1)
        return coh_between(ctx, disc_tree(1), [wire], p, p)

    def horizontal(word):
        if len(word) == 1:
            return word[0]
        cut = len(word) // 2
        return comp2(ctx, 0, horizontal(word[:cut]), horizontal(word[cut:]))

    lanes, offset = [], 0
    for i, width in enumerate(widths):
        parts = []
        for half in range(width):
            def edge():
                return arrow(objects[offset], objects[offset + 1])

            if i % 2:
                q, p = edge(), edge()
                row = {"t": arrow(q, p), "q": identity(q), "p": identity(p), "wire": p}
                if half == 0:
                    row["d"] = arrow(p, p)
                if half + 1 == width:
                    row["e"] = arrow(p, p)
            else:
                s, t = edge(), edge()
                row = {l: arrow(s, t) for l in "lmr"}
                if i not in (0, 2 * k):
                    q = edge()
                    row.update(t=arrow(q, s), q=identity(q))
            parts.append(row)
            offset += 1
        lanes.append(parts)

    for name, ports in ordinary_rules.items():
        faces = [[], []]
        for i, pair in sorted(ports.items()):
            for row in lanes[i]:
                for side, letter in enumerate(pair):
                    faces[side].append(row[letter] if letter and letter in row
                                       else row["q" if name == "Z" else "p"])
        last = arrow(*map(horizontal, faces))

    left, right = lanes[2 * seam + 1]
    tree = glue_tree(2, 0, 2)
    paste = tree_ctx(tree)
    x, y = map(v, maximal_vars(paste))
    before = comp2(paste, 1, comp2(paste, 0, x, src(paste, y)),
                   comp2(paste, 0, tgt(paste, x), y))
    after = comp2(paste, 1, comp2(paste, 0, src(paste, x), y),
                  comp2(paste, 0, x, tgt(paste, y)))
    switch = coh_between(ctx, tree, [left["d"], right["e"]], before, after)
    check_ctx(ctx)
    assert src(ctx, switch) != tgt(ctx, switch)
    return ctx, last, switch


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path)
    args = parser.parse_args()
    print("Local charts classified:", sum(local_graph(n, m) for n in (1, 2, 3) for m in range(3)))
    for k in (2, 3):
        for repeated in (False, True):
            ring_label(k, 0, repeated)
    ctx, bridge, switch = six_seam_terms()
    if args.agda:
        emitter = Emitter()
        emitter.check_typed("bridge", ctx, bridge)
        emitter.check_typed("split-wire-interchange", ctx, switch)
        args.agda.write_text(emitter.module(args.agda.stem, "Distributed seam on a six-seam ring."))
