"""Remove a right globe factor from a CaTT comparison at literal poles."""

from argparse import ArgumentParser
from functools import cache
from pathlib import Path

from catt import (arr, check_ctx, comp2, disc_tree, infer, src, sub_from,
                  subst_tm, subst_ty, tdim_tm, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity


def disk(rank):
    context = tree_ctx(disc_tree(rank))
    return context, v(len(context) - 1)


def face(context, term, rank, positive):
    while tdim_tm(context, term) > rank:
        term = tgt(context, term) if positive else src(context, term)
    return term


def instance(context, template, term):
    generic, top = disk(tdim_tm(context, term))
    return subst_tm(template, sub_from(generic, context, {top[1]: term}))


def right_unit(context, term):
    rank = tdim_tm(context, term)
    unit = face(context, term, 0, True)
    for _ in range(rank):
        unit = identity(context, unit)
    return comp2(context, 0, term, unit) if rank else term


def align(context, cell, original_source, original_target, cuts):
    for cut in cuts:
        s = face(context, original_source, cut, False)
        t = face(context, original_target, cut, True)
        before, after = disk_adjustments(cut)
        cell = comp2(context, cut, instance(context, before, s), cell)
        cell = comp2(context, cut, cell, instance(context, after, t))
    return cell


@cache
def disk_adjustments(rank):
    """Two unit corrections on a generic disk after all lower poles agree."""
    context, top = disk(rank)
    padded = align(context, right_unit(context, top), top, top, range(1, rank))
    return head(context, top, padded), head(context, padded, top)


def remove_globe(context, comparison, u, v_term):
    rank = tdim_tm(context, u)
    assert src(context, comparison) == right_unit(context, u)
    assert tgt(context, comparison) == right_unit(context, v_term)
    return align(context, comparison, u, v_term, range(1, rank + 1))


def append_globe(context, rank, vertex):
    generic, top = disk(rank)
    inclusion = [vertex]
    extended = context
    for ty in generic[1:]:
        new_type = subst_ty(ty, inclusion)
        inclusion.append(v(len(extended)))
        extended += (new_type,)

    collapse = list(map(v, range(len(context))))
    units = [vertex]
    for _ in range(rank):
        units.append(identity(context, units[-1]))
    for i in range(1, len(generic)):
        collapse.append(units[tdim_tm(generic, v(i))])
    return extended, inclusion[top[1]], collapse


def verify(context, u, v_term, emitter, name):
    rank = tdim_tm(context, u)
    assert infer(context, u) == infer(context, v_term)
    extended, marker, collapse = append_globe(context, rank, face(context, u, 0, True))
    check_ctx(extended)
    left = comp2(extended, 0, u, marker)
    right = comp2(extended, 0, v_term, marker)
    assert infer(extended, left) == infer(extended, right)
    assert top_counts(extended, left) == top_counts(extended, right)
    assert top_counts(extended, left)[marker[1]] == 1
    assert subst_tm(left, collapse) == right_unit(context, u)
    assert subst_tm(right, collapse) == right_unit(context, v_term)

    # The one-generator version has two different strict n-faces. Its
    # collapse must give exactly the same raw hypothesis as the first test.
    taller, arrow, retract = append_globe(context, rank + 1, face(context, u, 0, True))
    check_ctx(taller)
    lower = comp2(taller, 0, u, src(taller, arrow))
    upper = comp2(taller, 0, v_term, tgt(taller, arrow))
    assert infer(taller, lower) == infer(taller, upper)
    assert subst_tm(lower, retract) == right_unit(context, u)
    assert subst_tm(upper, retract) == right_unit(context, v_term)
    if rank >= 2 and not top_counts(context, u):
        # Bring an arbitrarily high strict identity down to a first
        # identity: its base now has a single fresh top-dimensional atom.
        small, z, fold = append_globe(context, rank - 1, face(context, u, 0, True))
        unit = identity(small, z)
        for pole in (u, v_term):
            shifted = comp2(small, 0, pole, unit)
            assert not top_counts(small, shifted)
            assert top_counts(small, src(small, shifted))[z[1]] == 1
            assert subst_tm(shifted, fold) == right_unit(context, pole)
    # In the forward direction an actual old comparison gives the marked
    # filler by whiskering. Use a variable so the faces are independent.
    h_index = len(taller)
    forward_ctx = taller + (arr(infer(taller, u), u, v_term),)
    forward = comp2(forward_ctx, 0, v(h_index), arrow)
    assert infer(forward_ctx, forward) == arr(infer(taller, lower), lower, upper)
    assert top_counts(forward_ctx, forward) == {h_index: 1, arrow[1]: 1}

    # Treat the output of the residual intrinsic comparison as a hypothesis.
    # Its specialization is a single variable in this relative context.
    h_type = subst_ty(arr(infer(extended, left), left, right), collapse)
    with_h = context + (h_type,)
    h = v(len(context))
    result = remove_globe(with_h, h, u, v_term)
    expected = arr(infer(context, u), u, v_term)
    assert infer(with_h, result) == expected
    assert top_counts(with_h, result) == {h[1]: 1}
    if emitter is not None:
        emitter.check_type(name, with_h, result, expected)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    parser.add_argument('--certificate-rank', type=int, choices=range(1, 6), default=3,
                        help='greatest input rank emitted for Agda (default 3)')
    args = parser.parse_args()
    emitter = Emitter()
    # Test intrinsic and successively identity-padded strict values, with
    # distinct raw ends in each case. The point is the rank-zero support.
    count = 0
    for height in range(5):
        context, top = disk(height)
        u = top
        for rank in range(height, 6):
            if rank > height:
                u = identity(context, u)
            if not rank:
                continue
            v_term = head(context, src(context, u), tgt(context, u))
            if v_term == u:
                # Keep the same literal boundary while changing the writing.
                v_term = comp2(context, rank - 1, identity(context, src(context, u)), u)
            assert u != v_term
            verify(context, u, v_term, emitter if rank <= args.certificate_rank else None,
                   f'disk-{height}-{rank}')
            count += 1

    # The triangle is nonglobular. Use an identity-padded 2-cell with
    # composite source. Whiskering a unit gives its second raw writing.
    path = tree_ctx(((), ()))
    f, g = v(2), v(4)
    fg = comp2(path, 0, f, g)
    context = path + (infer(path, fg),)
    h = v(len(path))
    context += (arr(infer(context, fg), fg, h),)
    triangle = v(len(context) - 1)
    u = triangle
    for rank in range(2, 6):
        if rank > 2:
            u = identity(context, u)
        other = comp2(context, rank - 1, u, identity(context, tgt(context, u)))
        verify(context, u, other, emitter if rank <= args.certificate_rank else None,
               f'triangle-{rank}')
        count += 1

    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Specialized right globe and literal pole corrections.'))
    print(f'{count} comparisons at literal poles, including four triangle instances; top count one throughout')


if __name__ == '__main__':
    main()
