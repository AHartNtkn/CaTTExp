"""Check transport at an ordinary CaTT declaration attached to a diagonal word head."""
from argparse import ArgumentParser
from pathlib import Path

from catt import arr, chain_tree, coh_between, comp2, disc_tree, infer, maximal_vars, tgt, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_outer_units import word_only_weight


def check_transport(emitter):
    line = tree_ctx(chain_tree(3))
    f, g, h = map(v, maximal_vars(line))
    word = comp2(line, 0, comp2(line, 0, f, g), h)
    diagonal = head(line, word, word)
    unit = identity(line, word)
    assert word_only_weight(line, diagonal, {}) == 1
    assert word_only_weight(line, unit, {}) == 0

    out = head(line, diagonal, unit)
    back = head(line, unit, diagonal)
    loop = comp2(line, 2, out, back)
    enlarge = head(line, identity(line, diagonal), loop)
    shrink = head(line, loop, identity(line, diagonal))

    # An arbitrary declaration whose ends have different word-only readings.
    ctx = line + (arr(infer(line, unit), unit, diagonal),)
    cell = v(len(line))
    shifted = comp2(ctx, 2, cell, out)
    returned = comp2(ctx, 2, cell, loop)

    globe = disc_tree(3)
    disc = tree_ctx(globe)
    top = v(maximal_vars(disc)[0])
    padded = comp2(disc, 2, top, identity(disc, tgt(disc, top)))
    insert_unit = coh_between(ctx, globe, [cell], top, padded)
    contract_unit = coh_between(ctx, globe, [cell], padded, top)

    forward = comp2(ctx, 3, insert_unit, comp2(ctx, 2, cell, enlarge))
    backward = comp2(ctx, 3, comp2(ctx, 2, cell, shrink), contract_unit)

    for name, term, source, target in (
        ('shiftToIdentity', shifted, unit, unit),
        ('returnToWrittenFace', returned, unit, diagonal),
        ('forwardAtDeclaration', forward, cell, returned),
        ('backwardAtDeclaration', backward, returned, cell),
    ):
        expected = arr(infer(ctx, source), source, target)
        assert infer(ctx, term) == expected
        if emitter:
            emitter.check_type(name, ctx, term, expected)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda_dir else None
    check_transport(emitter)
    print('Checked distinct diagonal readings and four exact transport judgments.')
    if emitter:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        name = 'WordEndpoints'
        (args.agda_dir / (name + '.agda')).write_text(emitter.module(name, __doc__))
