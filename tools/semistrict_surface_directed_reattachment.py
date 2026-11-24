"""Build raw boundary transports and the directed return using an invertible change."""
from argparse import ArgumentParser
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, glue_tree, infer, maximal_vars,
                  src, sub_from, subst_tm, tgt, tree_ctx, v)
from catt_unit_ordered_exchange import temporal_words
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, string_tree
from relative_coherence_hidden_seam import identity


def specialize(ctx, shape, labels, boundaries):
    generic = tree_ctx(shape)
    tips = maximal_vars(generic)
    left, right = boundaries(generic, *map(v, tips))
    sigma = sub_from(generic, ctx, dict(zip(tips, labels, strict=True)))
    return subst_tm(head(generic, left, right), sigma)


def reverse_square(emitter):
    ctx = tree_ctx(glue_tree(2, 0, 2))
    a, b = map(v, maximal_vars(ctx))
    f, ff, g, gg = src(ctx, a), tgt(ctx, a), src(ctx, b), tgt(ctx, b)

    def declare(left, right):
        nonlocal ctx
        var = v(len(ctx))
        ctx += (arr(infer(ctx, left), left, right),)
        return var

    inv = declare(ff, f)
    insert = declare(identity(ctx, ff), comp2(ctx, 1, inv, a))
    delete = declare(comp2(ctx, 1, a, inv), identity(ctx, f))
    left, right = temporal_words(ctx, a, b, 0, 1)
    aw, bw = comp2(ctx, 0, a, g), comp2(ctx, 0, ff, b)
    iw, tail = comp2(ctx, 0, inv, gg), comp2(ctx, 0, a, gg)
    bw0, iw0 = comp2(ctx, 0, f, b), comp2(ctx, 0, inv, g)

    def pad(row, at_end):
        def faces(P, z):
            unit = identity(P, tgt(P, z) if at_end else src(P, z))
            return (z, comp2(P, 1, z, unit)) if at_end else (comp2(P, 1, unit, z), z)
        return specialize(ctx, disc_tree(2), [row], faces)

    def identity_whisker(x, y, reverse=False):
        def faces(P, p, q):
            ends = identity(P, comp2(P, 0, p, q)), comp2(P, 0, identity(P, p), q)
            return ends[::-1] if reverse else ends
        return specialize(ctx, glue_tree(1, 0, 1), [x, y], faces)

    def split(first, second, edge, reverse=False):
        def faces(P, p, q, h):
            ends = (comp2(P, 0, comp2(P, 1, p, q), h),
                    comp2(P, 1, comp2(P, 0, p, h), comp2(P, 0, q, h)))
            return ends[::-1] if reverse else ends
        return specialize(ctx, (((), ()), ()), [first, second, edge], faces)

    def regroup(entries, before, after):
        def build(P, axes, form):
            if isinstance(form, int):
                return axes[form]
            return comp2(P, 1, *(build(P, axes, part) for part in form))

        def faces(P, *axes):
            return build(P, axes, before), build(P, axes, after)
        return specialize(ctx, string_tree(1, [2] * len(entries)), entries, faces)

    opening = composite(ctx, 2, [identity_whisker(ff, gg), comp2(ctx, 0, insert, gg),
                                 split(inv, a, gg)])
    native = specialize(ctx, glue_tree(2, 0, 2), [inv, b],
                        lambda P, p, q: temporal_words(P, p, q, 0, 1)[::-1])
    closing = composite(ctx, 2, [split(a, inv, g, reverse=True), comp2(ctx, 0, delete, g),
                                 identity_whisker(f, g, reverse=True)])
    steps = [
        pad(left, True),
        comp2(ctx, 1, left, opening),
        regroup([aw, bw, iw, tail], ((0, 1), (2, 3)), ((0, (1, 2)), 3)),
        comp2(ctx, 1, comp2(ctx, 1, aw, native), tail),
        regroup([aw, iw0, bw0, tail], ((0, (1, 2)), 3), ((0, 1), (2, 3))),
        comp2(ctx, 1, closing, right),
        pad(right, False),
    ]
    proof = composite(ctx, 2, steps)
    for shift in (0, 1):
        boundary = arr(infer(ctx, left), left, right)
        assert infer(ctx, proof) == boundary
        emitter.check_type('return' + str(shift), ctx, proof, boundary)
        ctx, proof, left, right = susp_ctx(ctx), susp_tm(proof), susp_tm(left), susp_tm(right)


def displaced_pole(emitter):
    D = tree_ctx(disc_tree(2))
    a = v(maximal_vars(D)[0])
    f, g = src(D, a), tgt(D, a)
    line = tree_ctx(disc_tree(1))
    edge = v(maximal_vars(line)[0])
    padded = comp2(line, 0, edge, identity(line, tgt(line, edge)))
    sigma = sub_from(line, D, {edge[1]: f})
    out, back = (subst_tm(head(line, *ends), sigma) for ends in ((padded, edge), (edge, padded)))
    u = comp2(D, 1, out, a)
    transported = comp2(D, 1, back, u)
    fit, reverse = head(D, transported, a), head(D, a, transported)
    b = v(len(D))
    B = D + (infer(D, a),)
    second = sub_from(D, B, {a[1]: b})
    w = subst_tm(u, second)
    z = v(len(B))
    X = B + (arr(infer(B, u), u, w),)
    Z = B + (arr(infer(B, a), a, b),)
    assert src(X, u) != f and tgt(X, u) == g
    forward = comp2(Z, 1, out, z)
    backward = composite(X, 2, [reverse, comp2(X, 1, back, z), subst_tm(fit, second)])
    assert infer(Z, forward) == X[-1] and infer(X, backward) == Z[-1]
    old_again = subst_tm(forward, (*map(v, range(len(B))), backward))
    assert old_again != z and infer(X, old_again) == X[-1]
    emitter.check_type('atPaddedPole', Z, forward, X[-1])
    emitter.check_type('atVariablePole', X, backward, Z[-1])
    emitter.check_type('roundTrip', X, old_again, X[-1])


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    reverse_square(emitter)
    displaced_pole(emitter)
    if args.agda_dir:
        module = 'DirectedReattachment'
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        source = emitter.module(module, __doc__).replace('open import CaTTExp.Pure',
                                                          'open import CaTTExp.Gray.Pure')
        (args.agda_dir / (module + '.agda')).write_text(source)
    print('Checked both directed returns and the two substitutions at distinct written 1-poles.')
