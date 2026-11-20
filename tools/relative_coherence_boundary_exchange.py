"""Check oriented exchanges with empty ports and the two typed hexagon comparisons."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import permutations
from pathlib import Path

from catt import (STAR, arr, check_ctx, coh_between, comp2, comp_tree, disc_tree,
                  infer, maximal_vars, src, subst_tm, subst_ty, sub_from, tgt,
                  tree_ctx, v)
from emit_agda import Emitter
from rc2 import lfold
from relative_coherence_cut import top_counts
from relative_coherence_hidden_seam import identity
from relative_coherence_mixed_cylinder import sides

# b is a creation of f; d consumes g. There is no way to remove an f.
PORTS = {"b": ("", "f"), "d": ("g", "")}


def histories(path, births, deaths):
    if not (births or deaths):
        yield ()
    for gate, remaining in (("b", births), ("d", deaths)):
        if remaining:
            before, after = PORTS[gate]
            for offset in range(len(path) - len(before) + 1):
                if path.startswith(before, offset):
                    next_path = path[:offset] + after + path[offset + len(before):]
                    for rest in histories(next_path, births - (gate == "b"), deaths - (gate == "d")):
                        yield ((gate, offset), *rest)


def swap(word, i):
    (a, offset), (b, later) = word[i:i + 2]
    before, after = PORTS[a]
    if offset + len(after) > later:
        return None
    return (*word[:i], (b, later + len(before) - len(after)), (a, offset), *word[i+2:])


def finite_test(path, births, deaths):
    words = set(histories(path, births, deaths))
    graph = {w: {i: u for i in range(len(w) - 1) if (u := swap(w, i)) is not None}
             for w in words}
    counts = Counter()
    for w, edges in graph.items():
        for i, u in edges.items():
            assert u in words
            counts["arrows"] += 1
            for j, other in edges.items():
                if i >= j:
                    continue
                if j == i + 1:
                    assert graph[graph[u][j]][i] == graph[graph[other][i]][j]
                    counts["hexagons"] += 1
                else:
                    assert graph[u][j] == graph[other][i]
                    counts["squares"] += 1
    visiting = set()
    @cache
    def sink(w):
        assert w not in visiting
        visiting.add(w)
        choices = {sink(u) for u in graph[w].values()}
        visiting.remove(w)
        assert len(choices) <= 1
        return next(iter(choices), w)
    final = {sink(w) for w in words}
    print(f"{path}, {births} births, {deaths} deaths: {len(words)} words, "
          f"{len(final)} normal forms, {counts['arrows']} exchanges, "
          f"{counts['squares']} squares, {counts['hexagons']} hexagons.")


def typed_hexagon(emitter):
    tree = (disc_tree(1),) * 3
    paste = tree_ctx(tree)
    slots = [v(i) for i in maximal_vars(paste)]
    def between(a, b):
        return coh_between(paste, tree, slots, a, b)
    routes = {}
    for order in permutations(range(3)):
        faces = [src(paste, t) for t in slots]
        steps = []
        for j in order:
            faces[j] = slots[j]
            steps.append(comp_tree(tuple(disc_tree(int(i == j)) for i in range(3)), paste, faces))
            faces[j] = tgt(paste, slots[j])
        routes[order] = lfold(paste, 1, steps)
    def movie(indices):
        order = (0, 1, 2)
        changes = []
        for i in indices:
            other = list(order)
            other[i:i+2] = reversed(other[i:i+2])
            other = tuple(other)
            changes.append(between(routes[order], routes[other]))
            order = other
        assert order == (2, 1, 0)
        return lfold(paste, 2, changes)
    left, right = movie((0, 1, 0)), movie((1, 0, 1))
    assert infer(paste, left) == infer(paste, right) and left != right
    loops = (STAR, arr(STAR, v(0), v(0)), arr(STAR, v(0), v(0)))
    unit = identity(loops, v(0))
    ctx = (*loops, arr(loops[1], unit, v(1)), arr(loops[2], v(2), unit))
    check_ctx(ctx)
    for label, a, b in (("hexagon", left, right), ("reverseHexagon", right, left)):
        h = between(a, b)
        ty = arr(infer(paste, a), a, b)
        assert infer(paste, h) == ty
        power = v(1)
        for n in range(1, 8):
            values = (comp2(ctx, 0, power, v(4)), v(3), v(4))
            sub = sub_from(paste, ctx, dict(zip(maximal_vars(paste), values)))
            term = subst_tm(h, sub)
            boundary = subst_ty(ty, sub)
            assert infer(ctx, term) == boundary
            if n == 2:
                emitter.check_typed(label, ctx, term)
                emitter.check_type(label + "Poles", ctx, term, boundary)
            power = comp2(ctx, 0, power, v(1))


def transport_generator(emitter):
    # The new 3-generator connects distinct births on a loop.
    base = (STAR, arr(STAR, v(0), v(0)))
    birth = arr(base[1], identity(base, v(0)), v(1))
    ctx = (*base, birth, birth, arr(birth, v(2), v(3)))
    check_ctx(ctx)
    tree = disc_tree(3)
    disc = tree_ctx(tree)
    x = v(len(disc) - 1)
    A, B = src(disc, x), tgt(disc, x)
    f, g = src(disc, A), tgt(disc, A)
    ef, eg = identity(disc, f), identity(disc, g)
    moved = comp2(disc, 1, x, eg)

    # Construct the two changes on the generic 2-disc before substituting A or B.
    lower_tree = disc_tree(2)
    lower = tree_ctx(lower_tree)
    a = v(len(lower) - 1)
    left_change, right_change = identity(lower, src(lower, a)), identity(lower, tgt(lower, a))
    padded = comp2(lower, 1, a, right_change)
    ends = sides(lower, a, padded, [left_change], [right_change])
    change = coh_between(lower, lower_tree, [a], *ends)
    eA, eB = (subst_tm(change, sub_from(lower, disc, {a[1]: t})) for t in (A, B))
    left, right = sides(disc, x, moved, [ef, eA], [eg, eB])
    sub = sub_from(disc, ctx, {x[1]: v(4)})
    assert top_counts(ctx, subst_tm(moved, sub)) == {4: 1}
    for label, source, target in (("birthTransport", left, right), ("birthTransportBack", right, left)):
        h = subst_tm(coh_between(disc, tree, [x], source, target), sub)
        boundary = subst_ty(arr(infer(disc, source), source, target), sub)
        assert infer(ctx, h) == boundary and not top_counts(ctx, h)
        assert top_counts(ctx, boundary[2]) == top_counts(ctx, boundary[3]) == {4: 1}
        emitter.check_typed(label, ctx, h)
        emitter.check_type(label + "Poles", ctx, h, boundary)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path)
    args = parser.parse_args()
    for test in (("g", 2, 1), ("gg", 2, 2), ("gg", 3, 2), ("fggf", 2, 2)):
        finite_test(*test)
    emitter = Emitter()
    typed_hexagon(emitter)
    transport_generator(emitter)
    print("The transported 3-generator occurs once on each side of both checked mixed 4-terms.")
    print("Both hexagon directions type-check at empty ports and with flank powers 1 through 7.")
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, "Empty-port exchange hexagon."))
