"""Check the two-change 4-polygraph and its actual marked coefficient maps."""

import argparse
from itertools import combinations, permutations, product
from pathlib import Path

from catt import arr, chain_tree, check_ctx, comp2, fv_tm, fv_ty, infer, tdim_tm, v
from emit_agda import Emitter
from homotopy_polygraph_timed_charts import order_complex_betti
from homotopy_polygraph_guarded_ring import enumerate_guarded
from relative_coherence_middle_wire import check_context, comparison
from relative_coherence_spherical_fibres import ring
from relative_coherence_strip_fibres import Complex


def presentation():
    ctx = check_context()[:13]
    for a, b in ((9, 10), (11, 12)):
        face = arr(infer(ctx, v(a)), v(a), v(b))
        ctx += (face, face)
    left = [comp2(ctx, 0, v(i), v(6)) for i in (13, 14)]
    right = [comp2(ctx, 0, v(6), v(i)) for i in (15, 16)]
    for s, t in (left, right):
        ctx += (arr(infer(ctx, s), s, t),)
    check_ctx(ctx)
    first = comp2(ctx, 0, v(17), v(7))
    last = comp2(ctx, 0, v(5), v(18))
    f, g, h = v(5), v(6), v(7)
    bridge = comparison(ctx, chain_tree(3), [f, g, h],
                        comp2(ctx, 0, comp2(ctx, 0, f, g), h),
                        comp2(ctx, 0, f, comp2(ctx, 0, g, h)))
    witness = comp2(ctx, 1, first, comp2(ctx, 1, bridge, last))
    assert tdim_tm(ctx, witness) == 4
    support = set(fv_tm(witness))
    for index in reversed(range(len(ctx))):
        if index in support:
            support.update(fv_ty(ctx[index]))
    assert support == set(range(len(ctx)))
    return ctx, witness


def lower_charts(wide):
    rules = {'C': {0: ('a', 'b')}, 'D': {2: ('p', 'q')}}
    for marker in wide:
        rules[marker][1] = ('', '')
    model = Complex(('a', '', 'p'), ('b', '', 'q'), rules)
    label, = model.components
    return model, label


def forget_wire(history, keep):
    # The four-cell face substitutes a narrow generator whiskered with the wire
    # identity. On that lane its port disappears; upper/lower colours are
    # fixed by the temporal edge, so C and D still name the two active gates.
    return tuple((left, ''.join(k for k in wire if k == keep), right)
                 for left, wire, right in history)


def check_fibre():
    joint, labels = lower_charts('CD')
    assert joint.betti(labels) == (1, 1)
    sides = {}
    projections = {}
    for keep in 'CD':
        side, labels = lower_charts(keep)
        assert side.betti(labels) == (1,)
        projection = [side.index[forget_wire(h, keep)] for h in joint.cells]
        for i, facets in enumerate(joint.facets):
            assert {projection[j] for j in facets} == set(side.facets[projection[i]])
        sides[keep] = side
        projections[keep] = projection

    # The hocolim is indexed by one joint chart and two temporal serializations.
    # Each serialization has two independent one-marker coefficient factors.
    elements = [('joint', i) for i in range(len(joint.cells))]
    for order in ('CD', 'DC'):
        elements.extend((order, i, j) for i, j in product(range(len(sides[order[0]].cells)),
                                                         range(len(sides[order[1]].cells))))

    def below(x, y):
        if x == y:
            return False
        if y[0] == 'joint':
            return x[0] == 'joint' and y[1] in joint.ideal(x[1])
        if x[0] == 'joint':
            source = [projections[k][x[1]] for k in y[0]]
        elif x[0] == y[0]:
            source = x[1:]
        else:
            return False
        return all(j in sides[k].ideal(i) for k, i, j in zip(y[0], source, y[1:]))

    betti = order_complex_betti(elements, below)
    assert betti[:3] == (1, 0, 1) and not any(betti[3:])
    print(f'{len(joint.cells)} joint lower histories, {len(sides["C"].cells)} per unary side, '
          f'{len(elements)} decorated objects, mod-two Betti numbers {betti[:3]}.')


def check_split_bridge():
    start, end, rules, typed = ring(2)
    split = {k: ports for k, ports in rules.items() if k != 'Z'}
    split['X'] = {0: rules['Z'][0]}
    split['Y'] = {4: rules['Z'][4]}

    def typed_split(tier):
        return typed(tuple(w.replace('X', 'Z').replace('Y', 'Z') for w in tier))

    # X and Y independently denote the chosen copies of the two narrow
    # changes. The passive tape is read only by B in this presentation.
    base = enumerate_guarded((start, end, split, typed_split), 'ixyf', 'Q', 'U')
    label, = base.components
    assert base.betti(label) == (1,)
    marked = enumerate_guarded((start, end, rules, typed), 'ixyf', 'Q', 'U')
    label, = marked.components
    assert marked.betti(label) == (1, 1)
    assert not enumerate_guarded((start, end, rules, typed), 'ixyf', 'Q', 'U', accept='[acb]').cells
    print(f'Split passive bridge: {len(base.cells)} base histories with point homology, '
          f'{len(marked.cells)} unary coefficient histories with circle homology.')


def independent_moves(number, time_limit):
    """Cubical necklace cells for independent marked changes, through dimension two."""
    partitions = set()
    for sequence in permutations(range(number)):
        for cuts in product((False, True), repeat=number - 1):
            blocks = []
            block = 0
            for i, event in enumerate(sequence):
                block |= 1 << event
                if i == number - 1 or cuts[i]:
                    blocks.append(block)
                    block = 0
            partitions.add(tuple(blocks))

    cells = [[], [], []]
    for blocks in partitions:
        for dim in range(3):
            for internal in combinations(range(len(blocks) - 1), dim):
                bead = 1
                longest = 1
                for i in range(len(blocks) - 1):
                    bead = bead + 1 if i in internal else 1
                    longest = max(longest, bead)
                if longest <= time_limit:
                    cells[dim].append((blocks, internal))

    ranks = []
    for dim in (1, 2):
        indices = {cell: j for j, cell in enumerate(cells[dim - 1])}
        pivots = {}
        for blocks, internal in cells[dim]:
            column = 0
            for i in internal:
                keep = tuple(j for j in internal if j != i)
                column ^= 1 << indices[blocks, keep]  # Promote vertex i to a joint.
                merged = blocks[:i] + (blocks[i] | blocks[i + 1],) + blocks[i + 2:]
                shift = tuple(j - 1 if j > i else j for j in keep)
                column ^= 1 << indices[merged, shift]
            while column:
                pivot = column.bit_length()
                if pivot not in pivots:
                    pivots[pivot] = column
                    break
                column ^= pivots[pivot]
        ranks.append(len(pivots))
    counts = tuple(map(len, cells))
    assert counts[0] - ranks[0] == 1
    return counts, counts[1] - sum(ranks)


def check_time_bound():
    assert independent_moves(3, 2) == ((13, 18, 0), 6)
    assert independent_moves(3, 3) == ((13, 18, 6), 0)
    counts, b1 = independent_moves(4, 3)
    assert b1 == 0 and counts[2] > 0
    print('Three independent moves: six free loops at time length two, six square '
          'relations at length three. Four moves:', counts, 'cells through degree two.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    ctx, term = presentation()
    print(f'{len(ctx)} declarations and a full-support four-cell checked.')
    check_fibre()
    check_time_bound()
    check_split_bridge()
    if args.agda:
        emitter = Emitter()
        emitter.check_typed('two-changes', ctx, term)
        args.agda.write_text(emitter.module(args.agda.stem, 'Two changing sides of the middle wire.'))
