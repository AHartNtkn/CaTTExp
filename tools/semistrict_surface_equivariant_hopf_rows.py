"""Check the deck translates of the Hopf attachments and their joined quotient."""
from argparse import ArgumentParser
from itertools import permutations, product
from pathlib import Path

from catt import arr, comp2, infer, tdim, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_cover_transport import compare, context


def compose(a, b):
    return tuple(a[j] for j in b)


def inverse(a):
    return tuple(a.index(j) for j in range(len(a)))


class Relations:
    """Sparse echelon reduction of integral attachment rows after imposing order two."""

    def __init__(self):
        self.pivots = {}

    def reduce(self, vector):
        for index in sorted(self.pivots, reverse=True):
            if vector & (1 << index):
                vector ^= self.pivots[index]
        return vector

    def add(self, vector):
        vector = self.reduce(vector)
        if vector:
            self.pivots[vector.bit_length() - 1] = vector


def normal_cosets(group, relators):
    one = tuple(range(len(group[0])))
    conjugates = {compose(compose(g, r), inverse(g)) for r in relators for g in group}
    normal = {one}
    todo = [one]
    while todo:
        g = todo.pop()
        for r in conjugates:
            gr = compose(g, r)
            if gr not in normal:
                normal.add(gr)
                todo.append(gr)
    return {p: min(compose(p, n) for n in normal) for p in group}


def check_rows(group, generators, defining, hopf):
    one = tuple(range(len(group[0])))
    sheets = list(product(group, repeat=2))
    base = {s: i for i, s in enumerate(sheets)}
    raw, joined = Relations(), Relations()

    def bit(i, sheet):
        return 1 << (i * len(sheets) + base[sheet])

    def translate(sheet, pair):
        return tuple(compose(g, h) for g, h in zip(sheet, pair, strict=True))

    for sheet in sheets:
        for x, y in [*((x, x) for x in generators), *((r, one) for r in defining)]:
            row = bit(0, sheet) ^ bit(0, translate(sheet, (x, y)))
            raw.add(row)
            joined.add(row)
        for i, r in enumerate(hopf, 1):
            orbit = bit(0, translate(sheet, (r, one))) ^ bit(0, sheet)
            raw.add(bit(i, sheet) ^ orbit)
            joined.add(bit(i, sheet) ^ orbit)
            joined.add(bit(i, sheet))

    count = 0
    columns = (len(hopf) + 1) * len(sheets)
    for reduction, relations in ((raw, defining), (joined, defining + hopf)):
        cosets = normal_cosets(group, relations)
        assert columns - len(reduction.pivots) == len(set(cosets.values()))
        for first, second in product(sheets, repeat=2):
            def label(sheet):
                return cosets[compose(sheet[0], inverse(sheet[1]))]
            assert (not reduction.reduce(bit(0, first) ^ bit(0, second))) == (label(first) == label(second))
            count += 1
    # Test the actual class of each translated Hopf value before killing it.
    raw_cosets = normal_cosets(group, defining)
    for i, r in enumerate(hopf, 1):
        for sheet in sheets:
            assert (not raw.reduce(bit(i, sheet))) == (raw_cosets[r] == raw_cosets[one])
            assert not joined.reduce(bit(i, sheet))
    return count


def degree_six_faces():
    # Raise the top scalar of the two-letter context to rank five. Its declared
    # reverse letters give a literal commutator word before inverse attachments.
    lower, pole = context(2)
    lower = lower[:-1]
    sphere_type = arr(infer(lower, pole), pole, pole)
    ctx = lower + (sphere_type,)
    sphere, idle = v(len(lower)), identity(ctx, pole)
    word = v(1)
    for i in (2, 3, 4):
        word = comp2(ctx, 0, word, v(i))
    left = comp2(ctx, 0, comp2(ctx, 0, sphere, word), idle)
    right = comp2(ctx, 0, comp2(ctx, 0, idle, word), sphere)
    assert infer(ctx, left) == infer(ctx, right)
    assert tdim(infer(ctx, left)) + 1 == 5
    return ctx, left, right


def audit():
    group = list(permutations(range(3)))
    a, b = (1, 0, 2), (0, 2, 1)
    c = compose(a, b)
    cases = [([], []), ([], [c]), ([], [a]), ([c], [a]), ([c], [c]), ([], [c, a])]
    checks = sum(check_rows(group, [a, b], defining, hopf) for defining, hopf in cases)
    print(f'{checks} raw and joined comparisons matched independent normal-subgroup calculations.')

    # The two words occupy distinct left regular sheets in S3 but the same
    # left regular sheet after killing the 3-cycle. Read actual raw placements.
    parity_action = [[1, 0], [1, 0]]
    regular = [[group.index(compose(p, x)) for p in group] for x in (a, b)]
    for word, counts in [((1, 2), (6, 0)), ((2, 1), (6, 0)), ((1, 1), (0, 0)),
                         ((1, 2, 1), (6, 2)), ((-2, 1, 2, 1), (6, 0))]:
        before = compare(regular, [], word)
        after = compare(parity_action, [[1, 2]], word)
        assert (sum(i != j for i, j in enumerate(before)),
                sum(i != j for i, j in enumerate(after))) == counts
    print("Five pairs of written 4-faces matched their separate sheet readings in S3 and C2.")


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    audit()
    ctx, left, right = degree_six_faces()
    if args.agda_dir:
        emitter = Emitter()
        for name, term in [('beforeWord', left), ('afterWord', right)]:
            emitter.check_type(name, ctx, term, infer(ctx, left))
        (args.agda_dir / 'HopfRowFaces.agda').write_text(emitter.module('HopfRowFaces', __doc__))
