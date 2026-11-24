"""Check the marked Gray query construction and its ordinary boundary recovery."""
import argparse
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, glue_tree, infer, maximal_vars, src,
                  subst_tm, tgt, tree_ctx, v)
from catt_unit_ordered_exchange import temporal_words
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_cut import Cut
from relative_coherence_exchange_faces import head
from semistrict_surface_computad_folds import disc_head
from semistrict_surface_substitution_equivalences import recognizes_equivalence


def arrow(ctx, source, target):
    assert infer(ctx, source) == infer(ctx, target)
    return arr(infer(ctx, source), source, target)


def check_gray(emitter, k):
    base = tree_ctx(glue_tree(k+1, 1, k+1))
    p, u = map(v, maximal_vars(base))
    q, target, marker = (v(len(base) + i) for i in range(3))
    ctx = (*base, infer(base, p), infer(base, u), infer(base, u))

    check_branches(emitter, k, ctx, p, q, u, target, marker, f'disc{k}')


def check_branches(emitter, k, ctx, p, q, u, target, marker, label):
    def cut(a, b):
        return comp2(ctx, 1, a, b)

    start, end = cut(p, u), cut(q, marker)
    free, forced = v(len(ctx)), v(len(ctx)+1)
    ctx += (arrow(ctx, u, marker), arrow(ctx, cut(p, target), end))
    expected = arrow(ctx, start, end)
    extra = v(len(ctx))
    ordinary_input = ctx + (arrow(ctx, u, target),)
    carry = comp2(ordinary_input, 1, p, extra)
    proof = comp2(ordinary_input, k+1, carry, forced)
    assert infer(ordinary_input, proof) == expected
    emitter.check_type(f'rawInput-{label}', ordinary_input, proof, expected)
    surface_input = ctx + (arrow(ctx, p, q),)
    proof = comp2(surface_input, 1, extra, free)
    assert infer(surface_input, proof) == expected
    emitter.check_type(f'cubeReturn-{label}', surface_input, proof, expected)


def check_square(gray, raw):
    ctx = tree_ctx(glue_tree(2, 0, 2))
    p, q = temporal_words(ctx, *map(v, maximal_vars(ctx)), 0, 1)
    gray.check_type('nativeSquare', ctx, head(ctx, q, p), arrow(ctx, q, p))
    seam = tgt(ctx, p)
    assert seam[0] != 'v'
    g = v(len(ctx))
    ctx += (infer(ctx, seam),)
    boundary = arrow(ctx, seam, g)
    u, target, marker = (v(len(ctx) + i) for i in range(3))
    ctx += (boundary, boundary, boundary)
    check_branches(gray, 1, ctx, p, q, u, target, marker, 'square')

    # Cut at each of the two spatial edges and recover the diagonal rule
    # at a non-looping arrow of the walking 1-disc.
    objects = [i for i, ty in enumerate(ctx) if ty == STAR]
    disc = tree_ctx(disc_tree(1))
    for index in (1, 2):
        cut = Cut(ctx, objects[index:])
        labels = []
        for old in cut.indices:
            if old in (u[1], target[1], marker[1]):
                labels.append(v(2))
            elif old == g[1]:
                labels.append(v(1))
            elif infer(ctx, v(old))[1] == STAR:
                labels.append(v(0))
            else:
                labels.append(ident(disc, v(0)))
        def project(term):
            return subst_tm(cut.term(term), tuple(labels))
        assert project(seam) == v(0)
        left = project(comp2(ctx, 1, p, target))
        right = project(comp2(ctx, 1, q, marker))
        raw.check_type(f'actualRule{index}', disc, head(disc, left, right), arrow(disc, left, right))


def check_recovery(emitter, k):
    disc = tree_ctx(disc_tree(k+1))
    boundary = disc[:-1]
    u, target = map(v, maximal_vars(boundary))
    pole = u
    for _ in range(k):
        pole = src(boundary, pole)
    stationary = pole
    for _ in range(k):
        stationary = ident(boundary, stationary)
    alternate = disc_head(boundary, stationary)

    def padded(ctx, left, term):
        return comp2(ctx, 0, left, term)

    source = padded(boundary, stationary, u)
    end = padded(boundary, alternate, target)
    typed_extension = (*boundary, arrow(boundary, source, end))
    generic = head(disc, source, end)
    images = (*map(v, range(len(boundary))), generic)
    assert recognizes_equivalence(typed_extension, disc, images)
    emitter.check_type(f'recover{k}', disc, generic, typed_extension[-1])
    one = tree_ctx(disc_tree(k))
    top = v(len(one)-1)
    # Both sides now use the very same variable, as on the rule after cutting.
    stationary = v(0)
    for _ in range(k):
        stationary = ident(one, stationary)
    left = padded(one, stationary, top)
    right = padded(one, disc_head(one, stationary), top)
    emitter.check_type(f'cutRule{k}', one, head(one, left, right), arrow(one, left, right))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    gray, raw = Emitter(), Emitter()
    for k in range(1, 5):
        check_gray(gray, k)
        check_recovery(raw, k)
    check_square(gray, raw)
    if args.agda_dir:
        for module, emitter in [('GrayQueryEmbedding', gray), ('RawQueryRecovery', raw)]:
            body = emitter.module(module, __doc__)
            if emitter is gray:
                body = body.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure')
            (args.agda_dir / f'{module}.agda').write_text(body)
    print('Checked both Gray branches and the relative ordinary substitution in input degrees 2–5.')
