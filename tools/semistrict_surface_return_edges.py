"""Build the old comparison at a composite attachment and check its bare-square image."""
import sys
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import STAR, arr, comp2, glue_tree, infer, maximal_vars, src, subst_tm, subst_ty, tgt, tree_ctx, v
from catt_unit_ordered_exchange import temporal_words
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity


def check_native_square():
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts' / 'e6'))
    from interchange_free import FreeAlgebra, OPERATIONS

    algebra = FreeAlgebra([[[[]], [[]]]])
    arrows = set()
    for name in ('r', 't', 'h', 'iota'):
        for args in product(*(algebra.domain(d) for d in OPERATIONS[name].inputs)):
            cell = algebra.describe(name, args)
            if cell and cell.source != cell.target:
                arrows.add((cell.source, cell.target))
    # Reachability only uses endpoints. Close the relation under every
    # chronological composition and every matching lower whisker, without
    # bounding the length or weight of a candidate reverse.
    while True:
        before = set(arrows)
        arrows.update((s, t) for s, m in before for n, t in before if m == n and s != t)
        for s, t in before:
            for d in (1, 2, 3):
                for z in algebra.domain(d):
                    for side in ('left', 'right'):
                        op = 'comp3' if d == 3 else f'{side}{d}_3'
                        inputs = ((z, s), (z, t)) if side == 'left' else ((s, z), (t, z))
                        u, v = (algebra.table.get((op, pair)) for pair in inputs)
                        if u is not None and v is not None:
                            u, v = algebra.root(u), algebra.root(v)
                            if u != v:
                                arrows.add((u, v))
        if before == arrows:
            break
    tips = tuple(v for v in algebra.generators.values() if algebra.data[v].dimension == 3)
    native = algebra.describe('iota', tips)
    assert native.source != native.target and arrows == {(native.source, native.target)}


def attachment():
    ctx = (STAR, STAR)

    def declare(ty):
        nonlocal ctx
        index = len(ctx)
        ctx += (ty,)
        return v(index)

    x, y = v(0), v(1)
    arrows = [declare(arr(STAR, x, y)) for _ in range(4)]
    alpha, changed_alpha = [declare(arr(infer(ctx, arrows[0]), *arrows[:2])) for _ in range(2)]
    middle = declare(arr(infer(ctx, arrows[1]), *arrows[1:3]))
    beta, changed_beta = [declare(arr(infer(ctx, arrows[2]), *arrows[2:])) for _ in range(2)]
    start, end = (comp2(ctx, 1, a, middle) for a in (alpha, changed_alpha))
    update = declare(arr(infer(ctx, start), start, end))
    other = declare(arr(infer(ctx, beta), beta, changed_beta))
    return ctx, temporal_words(ctx, update, other, 1, 2)


def clamp():
    bare = tree_ctx(glue_tree(3, 1, 3))
    a, b = map(v, maximal_vars(bare))
    alpha, changed_alpha = src(bare, a), tgt(bare, a)
    beta, changed_beta = src(bare, b), tgt(bare, b)
    f, g, h = src(bare, alpha), tgt(bare, alpha), tgt(bare, beta)
    pad = identity(bare, g)
    labels = (src(bare, f), tgt(bare, f), f, g, g, h, alpha, changed_alpha, pad,
              beta, changed_beta, comp2(bare, 1, a, pad), b)
    return bare, labels


def check_types(emitter):
    ctx, words = attachment()
    bare, labels = clamp()
    for shift in range(3):
        assert len(labels) == len(ctx)
        for i, t in enumerate(labels):
            assert infer(bare, t) == subst_ty(ctx[i], labels)
        assert infer(ctx, words[0]) == infer(ctx, words[1])
        reverse_type = arr(infer(ctx, words[0]), *words)
        returned = ctx + (arr(STAR, v(1), v(0)),)
        new_edge = v(len(ctx))
        assert infer(returned, new_edge) == arr(STAR, v(1), v(0))
        for word in words:
            assert infer(returned, word) == infer(ctx, word)
        images = tuple(subst_tm(t, labels) for t in words)
        assert infer(bare, images[0]) == infer(bare, images[1])
        assert images[0] != images[1]
        if shift == 0:
            for i, term in enumerate(words):
                emitter.check_typed('word' + str(i), returned, term)
                emitter.check_typed('clamped' + str(i), bare, images[i])
            for name, context, target_type in (('old', returned, reverse_type),
                                               ('bare', bare, subst_ty(reverse_type, labels))):
                c, ty = emitter.ctx(context), emitter.ty(target_type)
                emitter.checks.append(f'{name}Boundary : {c} ⊢ty {ty}\n'
                                      f'{name}Boundary = from-just (checkTy {c} (from-just (checkCtx {c})) {ty})\n')
        ctx, bare = susp_ctx(ctx), susp_ctx(bare)
        labels = (v(0), v(1)) + tuple(map(susp_tm, labels))
        words = tuple(map(susp_tm, words))


def paths(edges, depth):
    current = [(p, p, ()) for p in range(3)]
    result = set(current)
    for _ in range(depth):
        current = [(s, q, w + (name,)) for s, t, w in current for name, (p, q) in edges.items() if t == p]
        result.update(current)
    return result


def check_zero_fibres():
    # Two old 2-generators, one replacing a composite by an edge, the other
    # creating and consuming an old loop through consecutive rewrite steps.
    edges = {'a': (0, 1), 'b': (1, 2), 'c': (0, 2), 'l': (1, 1)}
    moves = [(0, ('a', 'b'), ('c',)), (1, (), ('l',)), (1, ('l',), ())]
    old = paths(edges, 5)
    enlarged = dict(edges, r=(2, 0))
    new = paths(enlarged, 5)

    def histories(table, alphabet):
        steps = set()
        for s, t, word in table:
            vertex = s
            for offset in range(len(word) + 1):
                for index, (at, lhs, rhs) in enumerate(moves):
                    if at == vertex and word[offset:offset+len(lhs)] == lhs:
                        target = word[:offset] + rhs + word[offset+len(lhs):]
                        if (s, t, target) in table:
                            steps.add((s, t, word, offset, index, target))
                if offset < len(word):
                    vertex = alphabet[word[offset]][1]
        return steps

    old_steps, new_steps = histories(old, edges), histories(new, enlarged)
    assert {(s, t, w) for s, t, w in new if 'r' not in w} == old
    assert all(w.count('r') == z.count('r') for _, _, w, _, _, z in new_steps)
    assert {m for m in new_steps if 'r' not in m[2]} == old_steps
    # The bound on the enumeration is enough to check graph connectivity.
    assert {(s, t) for s, t, _ in new} == set(product(range(3), repeat=2))
    assert (2, 0) not in {(s, t) for s, t, _ in old}
    return len(new_steps), len(old_steps)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    check_native_square()
    check_types(emitter)
    count, zero = check_zero_fibres()
    print(f'Checked the raw boundary and clamp at ranks 4–6, and {count} rewrite steps with {zero} of weight zero.')
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        source = emitter.module('ReturnEdges', __doc__)
        (args.agda_dir / 'ReturnEdges.agda').write_text(
            source.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))


if __name__ == '__main__':
    main()
