"""Read the two old placements of a four-sphere along a word in a permutation cover."""

from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import permutations, product
import json
from pathlib import Path

from catt import STAR, arr, comp2, infer, tdim, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_mixed_winding import slots


@cache
def context(generators):
    # Include a reverse letter for each edge. Relations constrain the allowed actions.
    ctx = (STAR,) + (arr(STAR, v(0), v(0)),) * (2*generators)
    pole = v(0)
    for _ in range(3):
        pole = identity(ctx, pole)
    ty = arr(infer(ctx, pole), pole, pole)
    return ctx + (ty,), identity(ctx, pole)


def placements(generators, word):
    ctx, unit = context(generators)
    sphere = v(len(ctx)-1)
    letters = [v(abs(i) + (generators if i < 0 else 0)) for i in word]
    path = letters[0] if letters else identity(ctx, v(0))
    for letter in letters[1:]:
        path = comp2(ctx, 0, path, letter)
    def place(left, right):
        return comp2(ctx, 0, comp2(ctx, 0, left, path), right)
    left, right = place(sphere, unit), place(unit, sphere)
    assert infer(ctx, left) == infer(ctx, right)
    return ctx, left, right


def inverse(perm):
    out = [0] * len(perm)
    for i, j in enumerate(perm):
        out[j] = i
    return out


def reader(perms):
    arrows = [*perms, *(inverse(p) for p in perms)]
    def read(term, sheet):
        if term[0] == 'v':
            i = term[1]
            if 1 <= i <= len(arrows):
                return arrows[i-1][sheet], Counter()
            return sheet, Counter({sheet: 1}) if i == len(arrows)+1 else Counter()
        _, arity, ty, sub = term
        first, _ = slots(arity)
        starts = []
        end = sheet
        for pos, i in first.items():
            if len(pos) == 1:
                starts.append(end)
                end, _ = read(sub[i], end)
        loads = Counter()
        if tdim(ty) + 1 == 4:
            for pos, i in first.items():
                if len(pos) == 4:
                    _, contribution = read(sub[i], starts[pos[0]])
                    loads.update(contribution)
        return end, loads
    return read


def compare(perms, relators, word):
    if not perms or not perms[0]:
        raise ValueError('provide at least one permutation on a nonempty sheet set')
    sheets = list(range(len(perms[0])))
    if any(sorted(p) != sheets for p in perms):
        raise ValueError('each entry must permute the same sheets')
    if any(not isinstance(i, int) or not 1 <= abs(i) <= len(perms)
           for w in [*relators, word] for i in w):
        raise ValueError('words use nonzero signed generator indices')
    negative = [inverse(p) for p in perms]
    def endpoint(w, start):
        for i in w:
            start = (perms if i > 0 else negative)[abs(i)-1][start]
        return start
    if any(endpoint(w, s) != s for w in relators for s in sheets):
        raise ValueError('the given sheet action violates a relator')
    _, left, right = placements(len(perms), word)
    read = reader(perms)
    ends = []
    for s in sheets:
        t = endpoint(word, s)
        assert read(left, s) == (t, Counter({s: 1}))
        assert read(right, s) == (t, Counter({t: 1}))
        ends.append(t)
    return ends


def audit():
    # The regular action of the generators (12),(123) on the six permutations.
    group = list(permutations(range(3)))
    perms = [[group.index(tuple(g[h[i]] for i in range(3))) for g in group]
             for h in ((1, 0, 2), (1, 2, 0))]
    relations = [[1, 1], [2, 2, 2], [1, 2, 1, 2]]
    count = 0
    for length in range(4):
        for w in product((1, -1, 2, -2), repeat=length):
            compare(perms, relations, w)
            count += len(group)
    assert compare([[1, 0]], [[1, 1]], [1, 1]) == [0, 1]
    return count


def baumslag_solitar():
    # Traversal order: t b^2 = b^3 t. Check every assignment on up to five sheets.
    actions = 0
    commutator = [1, 2, 1, -2, -1, 2, -1, -2]
    for size in range(1, 6):
        for b, t in product(permutations(range(size)), repeat=2):
            if all(b[b[t[i]]] == t[b[b[b[i]]]] for i in range(size)):
                assert compare([b, t], [[2, 1, 1, -2, -1, -1, -1]], commutator) == list(range(size))
                actions += 1
    return actions


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path, help='JSON with permutations, relators and word')
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    if args.input is None:
        print(f'Checked both raw placements at {audit()} sheet–word pairs in the regular S3 action.')
        print(f'Checked the old commutator comparison in all {baumslag_solitar()} BS(2,3) actions on up to five sheets.')
    else:
        data = json.loads(args.input.read_text())
        try:
            ends = compare(data['permutations'], data['relators'], data['word'])
        except ValueError as error:
            parser.error(str(error))
        print(f'Ending sheets {ends}; separating starting sheets {[s for s,t in enumerate(ends) if s != t]}.')
    if args.agda_dir:
        ctx, left, right = placements(2, [1, 2, -1, -2])
        emitter = Emitter()
        for name, term in [('beforeWord', left), ('afterWord', right)]:
            emitter.check_type(name, ctx, term, infer(ctx, left))
        (args.agda_dir / 'CoverTransport.agda').write_text(emitter.module('CoverTransport', __doc__))
