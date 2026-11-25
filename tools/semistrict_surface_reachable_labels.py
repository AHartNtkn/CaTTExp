"""Check elimination of variable-faced top generators by reachable component labels."""
from argparse import ArgumentParser
from itertools import permutations, product
from pathlib import Path

from catt import arr, comp2, infer, maximal_vars, src, subst_tm, tgt, tree_ctx, v
from ct_suspension import ident, susp_tm
from relative_coherence_exchange_faces import composite, head, string_tree
from semistrict_surface_directed_power_queries import apply, square
from semistrict_surface_inverse_completion import DerivationEmitter
from semistrict_surface_positional_tags import loop_tower
from semistrict_surface_top_string_tester import check_map


def reachable(size, edges):
    future = [{i} for i in range(size)]
    for a, b in edges:
        future[a].add(b)
    for middle in range(size):
        for row in future:
            if middle in row:
                row.update(future[middle])
    return future


def check_components():
    # Compare the reachability-and-multiset test to actual walks on two positions,
    # including an independent directed exchange of their chronological order.
    edges = tuple(permutations(range(3), 2))
    for mask in range(1 << len(edges)):
        graph = [edge for i, edge in enumerate(edges) if mask & (1 << i)]
        future = reachable(3, graph)
        rep = [min(b for b in row if a in future[b]) for a, row in enumerate(future)]
        for start in product(range(3), repeat=2):
            todo = [(False, start)]
            seen = set()
            while todo:
                reverse, pair = todo.pop()
                if (reverse, pair) in seen:
                    continue
                seen.add((reverse, pair))
                if not reverse:
                    todo.append((True, pair[::-1]))
                for i, x in enumerate(pair):
                    for a, b in graph:
                        if a == x:
                            todo.append((reverse, pair[:i] + (b,) + pair[i + 1:]))
            for end in product(range(3), repeat=2):
                goal = tuple(rep[e] for e in end)
                candidates = set(product(*({rep[x] for x in future[a]} for a in start)))
                for exchanged in (False, True):
                    wanted = goal[::-1] if exchanged else goal
                    assert ((exchanged, end) in seen) == (wanted in candidates)
                if sorted(rep[i] for i in start) == sorted(goal):
                    assert all(tuple(rep[i] for i in start) == p for p in candidates if sorted(p) == sorted(goal))


def check_replay(emitter):
    ctx = loop_tower(2)
    gate = v(2)
    pole = comp2(ctx, 1, gate, gate)
    ty = arr(infer(ctx, pole), pole, pole)
    names = [v(len(ctx) + i) for i in range(5)]
    ctx += (ty,) * len(names)
    a, b, c, d, e = names
    arcs = [(a, b), (b, a), (b, c), (c, d), (d, c), (c, e)]
    ab, _, bc, cd, _, ce = [v(len(ctx) + i) for i in range(len(arcs))]
    ctx += tuple(arr(ty, s, t) for s, t in arcs)
    native = susp_tm(square(2)[1])
    template = native[1], native

    def action(ambient, place, comparison, labels, face):
        arity = tree_ctx(string_tree(1, (4, 3) if place == 0 else (3, 4)))
        tips = list(map(v, maximal_vars(arity)))
        top = tips[place]
        ends = []
        for side in (src, tgt):
            tips[place] = side(arity, top)
            ends.append(face(arity, apply(arity, template, tips)))
        args = labels.copy()
        args[place] = comparison
        return apply(ambient, (arity, head(arity, *ends)), args)

    # At the two occurrences of a choose distinct future components c and e.
    # d and c are in the same component, so the final action recovers d.
    path_c = composite(ctx, 3, (ab, bc))
    path_e = composite(ctx, 3, (ab, bc, ce))
    old_source = src(ctx, apply(ctx, template, (a, a)))
    old_target = tgt(ctx, apply(ctx, template, (d, e)))
    stationary = apply(ctx, template, (c, e))
    steps = [action(ctx, 0, path_c, [a, a], src), action(ctx, 1, path_e, [c, a], src),
             stationary, action(ctx, 0, cd, [c, e], tgt)]
    replay = composite(ctx, 3, steps)
    expected = arr(infer(ctx, old_source), old_source, old_target)
    assert infer(ctx, replay) == expected

    base = loop_tower(2) + (ty,) * 3
    test = apply(base, template, (v(4), v(5)))
    section = tuple(map(v, range(3))) + (a, c, e)
    check_map(base, ctx, section)
    assert subst_tm(test, section) == stationary

    # Construct the two maps out of the entire cover. A given old arc may
    # have several copies; its chosen copy in a replay follows its final colour.
    future = reachable(len(names), [(names.index(x), names.index(y)) for x, y in arcs])
    cover = loop_tower(2)
    fold = list(map(v, range(len(cover))))
    evaluate = fold.copy()
    copies, arrows = {}, {}
    representatives = (a, c, e)
    for x, row in zip(names, future, strict=True):
        for i, colour in enumerate(representatives):
            if names.index(colour) in row:
                copies[x, colour] = v(len(cover))
                cover += (ty,)
                fold.append(x)
                evaluate.append(v(3 + i))
    for j, (x, y) in enumerate(arcs):
        for i, colour in enumerate(representatives):
            if (y, colour) in copies:
                arrows[x, y, colour] = v(len(cover))
                cover += (arr(ty, copies[x, colour], copies[y, colour]),)
                fold.append(v(len(ctx) - len(arcs) + j))
                evaluate.append(ident(base, v(3 + i)))
    fold, evaluate = tuple(fold), tuple(evaluate)
    check_map(cover, ctx, fold)
    check_map(cover, base, evaluate)
    lifted_c = composite(cover, 3, (arrows[a, b, c], arrows[b, c, c]))
    lifted_e = composite(cover, 3, (arrows[a, b, e], arrows[b, c, e], arrows[c, e, e]))
    final_labels = [copies[c, c], copies[e, e]]
    lifted = composite(cover, 3, [
        action(cover, 0, lifted_c, [copies[a, c], copies[a, e]], src),
        action(cover, 1, lifted_e, [copies[c, c], copies[a, e]], src),
        apply(cover, template, final_labels),
        action(cover, 0, arrows[c, d, c], final_labels, tgt)])
    assert subst_tm(lifted, fold) == replay
    collapsed = subst_tm(lifted, evaluate)
    assert infer(base, collapsed) == infer(base, test)
    if emitter is not None:
        emitter.check_type('stationaryComparison', base, test, infer(base, test))
        emitter.check_type('replayAtCompoundPoles', ctx, replay, expected)
        emitter.check_type('collapsedLift', base, collapsed, infer(base, test))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    check_components()
    emitter = DerivationEmitter() if args.agda_dir else None
    check_replay(emitter)
    if emitter is not None:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('ReachableLabels', __doc__).replace(
            'open import CaTTExp.Pure\n', 'open import CaTTExp.Gray.Pure\n'
            'open import CaTTExp.Pure using (∅)\n'
            'open import CaTTExp.PastingCheck ∅ using () renaming (checkPs to pastable)\n')
        (args.agda_dir / 'ReachableLabels.agda').write_text(module)
    print('Checked all 64 three-vertex graphs in both chronological orders and replayed the compound-pole example.')


if __name__ == '__main__':
    main()
