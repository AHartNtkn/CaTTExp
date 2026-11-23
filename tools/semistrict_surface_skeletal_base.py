"""Check the change of attaching boundary and the directed cutoff in Response 25."""
import argparse
from pathlib import Path

from catt import (STAR, arr, chain_tree, check_ctx, comp2, disc_tree, glue_tree,
                  infer, maximal_vars, sub_from, subst_tm, subst_ty, tree_ctx, v)
from emit_agda import Emitter
from rc_oracle import _top
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_scalar_cube import exchange


def path_pair(line):
    a, b, c = map(v, maximal_vars(line))
    left = comp2(line, 0, comp2(line, 0, a, b), c)
    right = comp2(line, 0, a, comp2(line, 0, b, c))
    return left, right


def graph_change(emitter):
    line = tree_ctx(chain_tree(3))
    left, right = path_pair(line)
    forward, backward = head(line, left, right), head(line, right, left)
    edges = tuple(map(v, maximal_vars(line)))
    # Fold the three formal edges to the same loop and attach two genuine 2-cells.
    graph = (STAR,) + (arr(STAR, v(0), v(0)),) * 3
    sigma = sub_from(line, graph, {e[1]: v(2) for e in edges})
    l, r, assoc = (subst_tm(t, sigma) for t in (left, right, forward))
    assert l != r
    arrow = graph[1]
    ctx = graph + (arr(arrow, v(1), l), arr(arrow, r, v(3)))
    check_ctx(ctx)
    paste = comp2(ctx, 1, comp2(ctx, 1, v(4), assoc), v(5))
    ty = arr(arrow, v(1), v(3))
    assert infer(ctx, paste) == ty and _top(ctx, paste) == {4: 1, 5: 1}
    emitter.check_type('joinedAtPath', ctx, paste, ty)

    # Change the 1-boundary of a 3-generator. First whisker it, then fit its
    # 2-faces using comparisons formed on the original linear arity.
    a = identity(line, left)
    b = comp2(line, 1, forward, backward)
    new = identity(line, right)
    diagram = line + (arr(infer(line, a), a, b),)
    h = v(len(line))
    moved = comp2(diagram, 1, comp2(diagram, 1, backward, h), forward)
    moved_ty = infer(diagram, moved)
    before = head(line, new, moved_ty[2])
    after = head(line, moved_ty[3], new)
    fitted = comp2(diagram, 2, comp2(diagram, 2, before, moved), after)
    context = graph + (subst_ty(diagram[-1], sigma),)
    folded = subst_tm(fitted, (*sigma, v(len(graph))))
    expected = subst_ty(arr(infer(line, new), new, new), sigma)
    check_ctx(context)
    assert infer(context, folded) == expected and _top(context, folded) == {len(graph): 1}
    assert context[-1][1] != expected[1]
    emitter.check_type('changedLowerBoundary', context, folded, expected)


def gray_change(emitter):
    pair = tree_ctx(glue_tree(2, 0, 2))
    left, right = (v(i) for i in maximal_vars(pair))
    square = exchange(pair, left, right)
    square_ty = infer(pair, square)
    padded = comp2(pair, 2, square, identity(pair, square_ty[3]))
    assert square != padded and infer(pair, padded) == square_ty
    # The width-two data carry a nonidentity strict Gray 3-cell. Its unitor
    # is obtained at a single 3-disc and then evaluated on that actual square.
    disc = tree_ctx(disc_tree(3))
    var = v(len(disc) - 1)
    generic = comp2(disc, 2, var, identity(disc, disc[-1][3]))
    sigma = sub_from(disc, pair, {var[1]: square})
    to_square = subst_tm(head(disc, generic, var), sigma)
    from_square = subst_tm(head(disc, var, generic), sigma)
    ctx = pair + (arr(square_ty, square, square),)
    h = v(len(pair))
    out = comp2(ctx, 3, comp2(ctx, 3, to_square, h), from_square)
    expected = arr(square_ty, padded, padded)
    check_ctx(ctx)
    assert infer(ctx, out) == expected and _top(ctx, out) == {len(pair): 1}
    emitter.check_type('changedSquare', ctx, out, expected)
    emitter.check_type('directedSquare', pair, square, square_ty)
    return pair, head(pair, square_ty[3], square_ty[2])


def right_unit(context, cell, rank, insert):
    disc = tree_ctx(disc_tree(rank))
    var = v(len(disc) - 1)
    padded = comp2(disc, rank - 1, var, identity(disc, disc[-1][3]))
    source, target = (var, padded) if insert else (padded, var)
    labels = sub_from(disc, context, {var[1]: cell})
    return subst_tm(head(disc, source, target), labels)


def changed_presentations(emitter):
    edge = arr(STAR, v(0), v(1))
    graph = (STAR, STAR, edge, edge)
    a, h = v(4), v(5)
    contexts = []
    for weak in (False, True):
        f, g = v(2), v(3)
        if weak:
            unit = identity(graph, v(1))
            f, g = (comp2(graph, 0, t, unit) for t in (f, g))
        face = arr(edge, f, g)
        ctx = graph + (face,)
        first = comp2(ctx, 1, a, identity(ctx, g)) if weak else a
        contexts.append(ctx + (arr(face, first, a),))
    for source_weak in (False, True):
        source, target = contexts if not source_weak else contexts[::-1]
        before = right_unit(target, v(2), 1, insert=not source_weak)
        after = right_unit(target, v(3), 1, insert=source_weak)

        def fit(cell):
            return comp2(target, 1, comp2(target, 1, before, cell), after)

        image = fit(a)
        if source_weak:
            image_h = comp2(target, 2, right_unit(target, image, 2, insert=False), fit(h))
        else:
            image_h = fit(comp2(target, 2, right_unit(target, a, 2, insert=True), h))
        labels = [v(i) for i in range(4)] + [image, image_h]
        check_ctx(source)
        for ty, term in zip(source, labels):
            assert infer(target, term) == subst_ty(ty, labels)
        assert _top(target, image) == {4: 1} and _top(target, image_h) == {5: 1}
        emitter.check_type('toLiteral' if source_weak else 'toPadded',
                           target, image_h, subst_ty(source[-1], labels))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    graph_change(emitter)
    changed_presentations(emitter)
    pair, reverse = gray_change(emitter)
    if args.agda_dir:
        for name, module_import in [('Ordinary', 'CaTTExp.Pure'), ('Gray', 'CaTTExp.Gray.Pure')]:
            module = name + 'SkeletalBase'
            if name == 'Gray':
                expression = emitter.tm(reverse)
                context = emitter.ctx(pair)
                emitter.checks.append(
                    f'reverse-rejected : infer {context} {expression} ≡ nothing\n'
                    'reverse-rejected = refl\n')
            code = emitter.module(module, __doc__)
            (args.agda_dir / (module + '.agda')).write_text(
                code.replace('open import CaTTExp.Pure', 'open import ' + module_import))
    print('Verified two attached 2-cells, a transported 3-generator, and a 4-generator on a Gray square, and both changes of presentation.')


if __name__ == '__main__':
    main()
