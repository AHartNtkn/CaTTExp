"""Check the reflected seam ring and its CaTT involution in Response 13."""
import argparse
from functools import cache
from pathlib import Path
from string import ascii_uppercase

from catt import STAR, arr, chain_tree, check_ctx, comp_tree, disc_tree, infer, sub_from, tdim
from catt import tree_ctx, tree_of, v
from emit_agda import Emitter
from relative_coherence_coloured_faces import visible
from relative_coherence_spherical_fibres import ring as original_ring
from relative_coherence_strip_fibres import Complex


def ring(k):
    ends = (0, 2 * k)
    ordinary, initial, final = [], [], []
    for j in range(2 * k + 1):
        if j in ends:
            lower = {c: ("u", "p") for c in "lmr"}
            upper = {c: ("p", "v") for c in "ijk"}
            letters, start, finish = lower | upper, "li", "rk"
        else:
            if j % 2:
                lower = {c: ("p", "p") for c in "de"}
                entry = exit_edge = "p"
                start, finish = "tdu", "teu"
            else:
                lower = {c: ("u", "v") for c in "lmr"}
                entry, exit_edge = "u", "v"
                start, finish = "tlu", "tru"
            letters = lower | {"t": ("x", entry), "u": (exit_edge, "y")}
        ordinary.append(letters)
        initial.append(start)
        final.append(finish)

    rules = {}
    for i in range(k):
        left, seam, right = 2 * i, 2 * i + 1, 2 * i + 2
        a, b = ascii_uppercase[2 * i:2 * i + 2]
        rules[a] = {left: ("mj", "rk") if left == 0 else ("m", "r"), seam: ("d", "")}
        rules[b] = {seam: ("", "e"), right: ("li", "mj") if right == ends[1] else ("l", "m")}
    for name, start, middle, finish in (("Y", "l", "m", "r"), ("Z", "i", "j", "k")):
        rules[name] = {j: ("", "") for j in range(2 * k + 1)}
        rules[name][0] = (start, middle)
        rules[name][ends[1]] = (middle, finish)
    return ordinary, tuple(initial), tuple(final), rules


def empty_edge(event):
    return {"Y": "x", "Z": "y"}.get(event, "p")


def charts(k):
    lanes, start, finish, rules = ring(k)
    annotated = [lane.copy() for lane in lanes]
    for event, span in rules.items():
        for j, (word, _) in span.items():
            marker_type = (lanes[j][word[0]][0], lanes[j][word[-1]][1]) if word else (empty_edge(event),) * 2
            annotated[j][event] = marker_type

    def well_typed(tier):
        for j, word in enumerate(tier):
            edge = lanes[j][start[j][0]][0]
            for ch in word:
                source, target = annotated[j][ch]
                if edge != source:
                    return False
                edge = target
            if edge != lanes[j][finish[j][-1]][1]:
                return False
        return True

    model = Complex(start, finish, rules, well_typed)
    assert len(model.components) == 1
    assert model.betti(model.components[0]) == (1,) + (0,) * (k - 2) + (1,)
    for i, cell in enumerate(model.cells):
        reflected = tuple(tuple(mirror_word(j, word, k) for j, word in enumerate(tier)) for tier in cell)
        other = model.index[reflected]
        assert other != i
        assert tuple(visible(reflected, k)) == tuple(-x for x in visible(cell, k))
        for facet in model.facets[i]:
            image = tuple(tuple(mirror_word(j, w, k) for j, w in enumerate(tier))
                          for tier in model.cells[facet])
            assert model.index[image] in model.facets[other]
    print(f"{k} seams: {len(model.cells)} cells, Betti {model.betti(model.components[0])}, "
          "reflection reverses every visible sign and preserves every facet")


def mirror_word(j, word, k):
    pairs = "li mj rk" if j in (0, 2 * k) else "tu"
    switch = {c: p[1 - i] for p in (pairs + " YZ").split() for i, c in enumerate(p)}
    return "".join(switch.get(c, c) for c in reversed(word))


def original_fixed_cells(k):
    model = Complex(*original_ring(k))
    events = ascii_uppercase[:2 * k]
    table = str.maketrans(events + "lrde", events[::-1] + "rled")
    fixed = {}
    for i, cell in enumerate(model.cells):
        dual = tuple(tuple(word.translate(table) for word in reversed(tier)) for tier in reversed(cell))
        j = model.index[dual]
        signs = visible(cell, k)
        assert tuple(visible(dual, k)) == tuple(-x for x in reversed(signs))
        if i == j:
            fixed[i] = tuple(signs)

    # A fixed simplex of the barycentric subdivision is a chain of fixed cells.
    # The fixed cells need not be consecutive ranks in the original face poset.
    remaining = set(fixed)
    signs_by_component = []
    neighbors = {i: set() for i in fixed}
    for i in fixed:
        for j in model.ideal(i).intersection(fixed):
            neighbors[i].add(j)
            neighbors[j].add(i)
    while remaining:
        seed = remaining.pop()
        component, stack = {seed}, [seed]
        while stack:
            found = neighbors[stack.pop()] & remaining
            remaining.difference_update(found)
            component.update(found)
            stack.extend(found)
        signs_by_component.append({fixed[i][0] for i in component})
    # For two or three seams the fixed sign sphere is a pair of points.
    assert sorted(signs_by_component, key=min) == [{-1}, {1}]
    print(f"Original {k}-seam ring: {len(fixed)} fixed cells, two fixed-locus components")


def reversed_dimension(n):
    return n == 2 or n >= 4


def positions(tree, path=()):
    yield path + (0,)
    for i, subtree in enumerate(tree):
        yield path + (i + 1,)
        yield from positions(subtree, path + (i,))


def opposite_tree(tree, depth=1):
    children = tuple(opposite_tree(child, depth + 1) for child in tree)
    return children[::-1] if reversed_dimension(depth) else children


def opposite_position(tree, pos, depth=1):
    index, *rest = pos
    if not rest:
        return (len(tree) - index if reversed_dimension(depth) else index,)
    child = len(tree) - 1 - index if reversed_dimension(depth) else index
    return (child,) + opposite_position(tree[index], rest, depth + 1)


@cache
def opposite_arity(context):
    tree = tree_of(context)
    dual = opposite_tree(tree)
    target = {p: i for i, p in enumerate(positions(dual))}
    levels = tuple(target[opposite_position(tree, p)] for p in positions(tree))
    return tree_ctx(dual), levels


@cache
def opposite_term(term, levels):
    if term[0] == "v":
        return v(levels[term[1]])
    _, context, ty, args = term
    dual, order = opposite_arity(context)
    moved = [None] * len(args)
    for i, arg in enumerate(args):
        moved[order[i]] = opposite_term(arg, levels)
    return ("coh", dual, opposite_type(ty, order), tuple(moved))


@cache
def opposite_type(ty, levels):
    if ty == STAR:
        return STAR
    _, base, source, target = ty
    if reversed_dimension(tdim(ty) + 1):
        source, target = target, source
    return arr(opposite_type(base, levels), opposite_term(source, levels), opposite_term(target, levels))


def syntax(k):
    lanes, start, finish, rules = ring(k)
    ctx = ()

    def declare(ty):
        nonlocal ctx
        term = v(len(ctx))
        ctx += (ty,)
        return term

    def arrow(s, t):
        base = infer(ctx, s)
        assert base == infer(ctx, t)
        return declare(arr(base, s, t))

    objects = [declare(STAR) for _ in range(2 * k + 2)]
    dual = {x: x for x in objects}
    edges, gates = [], []
    for j, lane in enumerate(lanes):
        e = {a: arrow(objects[j], objects[j + 1]) for a in sorted({p for f in lane.values() for p in f})}
        g = {a: arrow(e[s], e[t]) for a, (s, t) in lane.items()}
        for a in e:
            dual[e[a]] = e[{"u": "v", "v": "u", "x": "y", "y": "x"}.get(a, a)]
        for a in g:
            dual[g[a]] = g[mirror_word(j, a, k)]
        edges.append(e)
        gates.append(g)

    def word(j, chars, event=None):
        if chars:
            return comp_tree((chain_tree(len(chars)),), ctx, [gates[j][ch] for ch in chars])
        disc = tree_ctx(disc_tree(1))
        top = v(len(disc) - 1)
        return ("coh", disc, arr(infer(disc, top), top, top),
                sub_from(disc, ctx, {top[1]: edges[j][empty_edge(event)]}))

    def across(words):
        return comp_tree(tuple(disc_tree(1) for _ in words), ctx, words)

    event_vars = {}
    for event, span in rules.items():
        faces = [across([word(j, pair[side], event) for j, pair in span.items()]) for side in (0, 1)]
        event_vars[event] = arrow(*faces)
    for name, term in event_vars.items():
        dual[term] = event_vars[{"Y": "Z", "Z": "Y"}.get(name, name)]
    levels = tuple(dual[v(i)][1] for i in range(len(ctx)))
    check_ctx(ctx)
    for i, ty in enumerate(ctx):
        assert levels[levels[i]] == i and opposite_type(ty, levels) == ctx[levels[i]]
    poles = tuple(across([word(j, chars) for j, chars in enumerate(words)]) for words in (start, finish))
    assert infer(ctx, poles[0]) == infer(ctx, poles[1])
    assert all(opposite_term(pole, levels) == pole for pole in poles)
    print(f"{k} seams: {len(ctx)} declarations and both weak poles pass literal duality")
    return ctx, event_vars["Z"], poles


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path)
    parser.add_argument("--three-seams", action="store_true", help="also enumerate the larger chart complexes")
    args = parser.parse_args()
    charts(2)
    original_fixed_cells(2)
    if args.three_seams:
        charts(3)
        original_fixed_cells(3)
    ctx, bridge, poles = syntax(6)
    if args.agda:
        emitter = Emitter()
        for label, term in zip(("bridge", "initial-pole", "final-pole"), (bridge, *poles)):
            emitter.check_typed(label, ctx, term)
        args.agda.write_text(emitter.module(args.agda.stem, "Six seams with a boundary-reversing involution."))
