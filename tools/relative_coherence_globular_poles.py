"""Lift a strict expression by comparing its raw poles on globular supports."""

from argparse import ArgumentParser
from graphlib import TopologicalSorter
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, disc_tree, fv_tm, fv_ty, infer,
                  src, subst_tm, subst_ty, tdim, tgt, tree_ctx, v)
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head
from relative_coherence_globe_padding import face
from relative_coherence_hidden_seam import identity


def position_order(context, support):
    order = TopologicalSorter()
    for i in support:
        order.add(i)
        ty = context[i]
        if ty != STAR:
            source, target = ty[2:]
            assert source[0] == target[0] == 'v'
            order.add(i, source[1])
            order.add(target[1], i)
    order.prepare()
    result = []
    while order.is_active():
        (next_position,) = order.get_ready()
        result.append(next_position)
        order.done(next_position)
    return result


def position_tree(dims, rank=0):
    ends = [i for i, d in enumerate(dims) if d == rank]
    assert ends and ends[0] == 0 and ends[-1] == len(dims) - 1
    return tuple(position_tree(dims[i + 1:j], rank + 1) for i, j in zip(ends, ends[1:]))


def compare(context, a, b):
    assert infer(context, a) == infer(context, b)
    support = set(fv_tm(a) | fv_tm(b))
    for i in reversed(range(len(context))):
        if i in support:
            support.update(fv_ty(context[i]))
    positions = position_order(context, support)
    arity = tree_ctx(position_tree([tdim(context[i]) + 1 for i in positions]))
    formal = position_order(arity, range(len(arity)))
    labels = dict(zip(formal, positions, strict=True))
    inclusion = tuple(v(labels[i]) for i in range(len(arity)))
    inverse = {ambient: v(i) for i, ambient in labels.items()}
    assert all(subst_ty(ty, inclusion) == context[labels[i]] for i, ty in enumerate(arity))
    generic = head(arity, subst_tm(a, inverse), subst_tm(b, inverse))
    return subst_tm(generic, inclusion)


def fit(context, cell, source, target=None):
    """Align both lower poles, then the specified pole(s) at the final cut."""
    rank = tdim(infer(context, source)) + 1
    for j in range(rank + 1):
        new_source = face(context, source, j, False)
        old_source = face(context, cell, j, False)
        if new_source != old_source:
            assert j > 0
            cell = comp2(context, j, compare(context, new_source, old_source), cell)
        if target is not None or j < rank:
            right = source if target is None else target
            new_target = face(context, right, j, True)
            old_target = face(context, cell, j, True)
            if old_target != new_target:
                assert j > 0
                cell = comp2(context, j, cell, compare(context, old_target, new_target))
    return cell


def lift(context, word):
    if word[0] == 'atom':
        return v(word[1])
    if word[0] == 'id':
        return identity(context, lift(context, word[1]))
    _, cut, left_word, right_word = word
    left = lift(context, left_word)
    right = fit(context, lift(context, right_word), face(context, left, cut, True))
    return comp2(context, cut, left, right)


def unary(context, term):
    disk = tree_ctx(disc_tree(1))
    result = ('coh', disk, disk[-1], (src(context, term), tgt(context, term), term))
    assert infer(context, result) == infer(context, term)
    return result


def verify(emitter):
    # Two triangles attached on h, with different actual writings of h.
    path = tree_ctx(((), ()))
    fg = comp2(path, 0, v(2), v(4))
    context = path + (infer(path, fg), STAR, arr(STAR, v(0), v(6)),
                      arr(STAR, v(6), v(3)))
    h = v(5)
    kl = comp2(context, 0, v(7), v(8))
    context += (arr(infer(context, fg), fg, h),
                arr(infer(context, h), unary(context, h), kl))
    u, w = unary(context, fg), unary(context, kl)
    for rank in range(2, 6):
        check_ctx(context)
        first, second = len(context) - 2, len(context) - 1
        assert tgt(context, v(first)) != src(context, v(second))
        assert u != src(context, v(first)) and w != tgt(context, v(second))
        word = ('comp', rank - 1, ('atom', first), ('atom', second))
        out = fit(context, lift(context, word), u, w)
        expected = arr(infer(context, u), u, w)
        assert infer(context, out) == expected
        assert top_counts(context, out) == {first: 1, second: 1}
        if rank <= 3:
            emitter.check_type('chain-' + str(rank), context, out, expected)
        context, u, w = susp_ctx(context), susp_tm(u), susp_tm(w)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    verify(emitter)
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Two triangles at prescribed poles.'))
    print('4 two-atom lifts in ranks 2 through 5; internal seam and both exterior poles corrected')
