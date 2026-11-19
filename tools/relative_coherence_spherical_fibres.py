"""Compare direct typed cube-chain enumeration to the sphere calculation in Response 8."""
from collections import Counter
from functools import cache
from string import ascii_uppercase
import sys

from relative_coherence_strip_fibres import Complex


def ring(k):
    lanes = range(2 * k + 1)
    ends = (0, 2 * k)
    letters = []
    initial = []
    final = []
    for j in lanes:
        if j % 2:
            types = {"t": ("q", "p"), "d": ("p", "p"), "e": ("p", "p")}
            initial.append("td")
            final.append("te")
        else:
            types = {x: ("u", "v") for x in "lmr"}
            if j not in ends:
                types["t"] = ("q", "u")
            prefix = "" if j in ends else "t"
            initial.append(prefix + "l")
            final.append(prefix + "r")
        letters.append(types)

    rules = {}
    for i in range(k):
        a, b = ascii_uppercase[2 * i:2 * i + 2]
        rules[a] = {2 * i: ("m", "r"), 2 * i + 1: ("d", "")}
        rules[b] = {2 * i + 1: ("", "e"), 2 * i + 2: ("l", "m")}
        letters[2 * i][a] = letters[2 * i + 2][b] = ("u", "v")
        letters[2 * i + 1][a] = letters[2 * i + 1][b] = ("p", "p")
    rules["Z"] = {j: ("", "") for j in lanes}
    rules["Z"][0] = ("l", "m")
    rules["Z"][2 * k] = ("m", "r")
    for j in lanes:
        letters[j]["Z"] = ("u", "v") if j in ends else ("q", "q")

    def well_typed(tier):
        for j, word in enumerate(tier):
            edge = "u" if j in ends else "q"
            for gate in word:
                source, target = letters[j][gate]
                if source != edge:
                    return False
                edge = target
            if edge != ("p" if j % 2 else "v"):
                return False
        return True

    return tuple(initial), tuple(final), rules, well_typed


def sheet_counts(k):
    """Count cells by temporal tiers, with one bit per still-visible seam order."""
    bridge = 2 * k
    full = (1 << (bridge + 1)) - 1
    predecessors = [0] * (bridge + 1)
    predecessors[0] = 1 << bridge
    predecessors[bridge] = 1 << (bridge - 1)
    for a in range(2, bridge, 2):
        predecessors[a] = 1 << (a - 1)

    @cache
    def visit(done):
        if done == full:
            return Counter({0: 1})
        enabled = sum(1 << i for i, pred in enumerate(predecessors)
                      if not (done >> i & 1) and pred & done == pred)
        result = Counter()
        tier = enabled
        while tier:
            bits = sum(bool(tier >> b & 1) and not (done >> (b - 1) & 1)
                       for b in range(1, bridge, 2))
            shift = tier.bit_count() - 1
            for degree, count in visit(done | tier).items():
                result[degree + shift] += count << bits
            tier = (tier - 1) & enabled
        return result

    return visit(0)


def catt_context(k):
    from catt import STAR, arr, check_ctx, comp2, disc_tree, infer, sub_from, tree_ctx, v

    ctx = ()

    def declare(ty):
        nonlocal ctx
        term = v(len(ctx))
        ctx += (ty,)
        return term

    def arrow(x, y):
        ty = infer(ctx, x)
        assert ty == infer(ctx, y)
        return declare(arr(ty, x, y))

    def identity(x):
        disc = tree_ctx(disc_tree(1))
        top = v(len(disc) - 1)
        return ("coh", disc, arr(infer(disc, top), top, top),
                sub_from(disc, ctx, {top[1]: x}))

    def horizontal(cells):
        if len(cells) == 1:
            return cells[0]
        cut = len(cells) // 2
        return comp2(ctx, 0, horizontal(cells[:cut]), horizontal(cells[cut:]))

    objects = [declare(STAR) for _ in range(2 * k + 2)]
    rows = []
    for j in range(2 * k + 1):
        def edge():
            return arrow(objects[j], objects[j + 1])

        if j % 2:
            q, p = edge(), edge()
            prefix = arrow(q, p)
            rows.append(dict(t=prefix, q=identity(q), p=identity(p), d=arrow(p, p), e=arrow(p, p)))
        else:
            u, w = edge(), edge()
            cells = {name: arrow(u, w) for name in "lmr"}
            if j not in (0, 2 * k):
                q = edge()
                cells["t"] = arrow(q, u)
                cells["q"] = identity(q)
            rows.append(cells)
    for i in range(k):
        left, seam, right = rows[2 * i:2 * i + 3]
        arrow(horizontal([left["m"], seam["d"]]), horizontal([left["r"], seam["p"]]))
        arrow(horizontal([seam["p"], right["l"]]), horizontal([seam["e"], right["m"]]))
    middle = [row["q"] for row in rows[1:-1]]
    bridge = arrow(horizontal([rows[0]["l"], *middle, rows[-1]["m"]]),
                   horizontal([rows[0]["m"], *middle, rows[-1]["r"]]))
    check_ctx(ctx)
    return ctx, bridge, rows


def check_other_labels():
    initial, final, rules, well_typed = ring(2)
    ordinary = list(initial)
    ordinary[1] = "tdd"
    end = list(final)
    end[1] = "tde"
    repeated = Complex(tuple(ordinary), tuple(end), rules, well_typed)
    betti = sorted(repeated.betti(c) for c in repeated.components)
    assert betti == [(1,), (1, 1)]
    print("repeated seam letters, component Betti numbers", betti)

    ordinary, end = list(initial), list(final)
    ordinary[0], end[-1] = "m", "m"
    del rules["Z"]
    sublabel = Complex(tuple(ordinary), tuple(end), rules, well_typed)
    assert len(sublabel.components) == 1 and sublabel.betti(sublabel.components[0]) == (1,)
    print("proper-support label, contractible homology", len(sublabel.cells), "cells")


def main():
    check_other_labels()
    for k in [2, 3, 4, 5]:
        cells = sheet_counts(k)
        assert sum((-1) ** d * n for d, n in cells.items()) == 1 + (-1) ** (k - 1)
        print("seams", k, "cell counts", sorted(cells.items()))
        if k <= 3:
            obj = Complex(*ring(k))
            assert len(obj.components) == 1 and Counter(obj.degrees) == cells
            betti = obj.betti(obj.components[0])
            assert betti == (1,) + (0,) * (k - 2) + (1,)
            print("direct typed enumeration over F2", betti)


if __name__ == "__main__":
    if sys.argv[1:] == ["--agda"]:
        from emit_agda import Emitter
        emitter = Emitter()
        context, bridge, _ = catt_context(4)
        emitter.check_typed("bridge", context, bridge)
        print(emitter.module("SphericalFibre", "Four-seam CaTT presentation."))
    else:
        main()
