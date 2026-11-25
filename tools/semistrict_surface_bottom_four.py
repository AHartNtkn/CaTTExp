"""Read bottom-sphere contributions to old degree-five comparisons."""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from itertools import combinations, permutations, product
import json
from pathlib import Path

from semistrict_surface_directed_top_counts import uses
from semistrict_surface_divisible_squares import diagonalize
from semistrict_surface_reversible_five import quotient


def hall_triples(rank):
    for i, j in combinations(range(rank), 2):
        for k in range(i, rank):
            yield j, i, k


def basis(r, s, t):
    if min(r, s, t) < 0:
        raise ValueError('sphere counts must be nonnegative')
    a = [f'a{i+1}' for i in range(r)]
    b = [f'b{i+1}' for i in range(s)]
    # (coordinate name, torsion order or zero, supported on the two-sphere wedge)
    rows = [(f'{x}.eta2.eta3', 2, True) for x in a]
    rows += [(f'[{y},{x}].eta3', 2, True) for x,y in combinations(a, 2)]
    rows += [(f'[[{a[j]},{a[i]}],{a[k]}]', 0, True) for j,i,k in hall_triples(r)]
    rows += [(f'{y}.eta3', 2, False) for y in b]
    rows += [(f'[{x},{y}]', 0, False) for x,y in product(a, b)]
    return rows + [(f'c{i+1}', 0, False) for i in range(t)]


def read(data):
    coords = basis(*data['spheres'])
    names = {name: i for i,(name, _, _) in enumerate(coords)}
    def vector(terms):
        result = [0] * len(coords)
        for name, value in terms.items():
            if name not in names or type(value) is not int:
                raise ValueError(f'invalid coordinate {name} with value {value!r}')
            result[names[name]] = value
        return result
    relations = [vector(terms) for terms in data.get('relations', [])]
    directed = [vector(terms) for terms in data.get('rules', [])]
    face = vector(data['face'])
    raw = relations + [vector({name: order}) for name, order, _ in coords if order]
    bound = raw + [vector({name: 1}) for name, _, bottom in coords if bottom]
    joined = bound + [vector({name: 1}) for name, order, bottom in coords if order and not bottom]
    counts = data.get('counts')
    def fills(rows):
        if not directed and counts is None:
            return not any(quotient(rows, face))
        return uses(rows, directed, face, counts) is not None
    old, possible, join = map(fills, (raw, bound, joined))
    return dict(raw=old, binary=True if old else None if possible else False, joined=join)


def tensor_bracket(j, i, k):
    # Graded commutator in the tensor algebra of the loop homology:
    # the first two letters are odd and their bracket is even.
    value = Counter()
    for term, sign in [((j,i,k), 1), ((i,j,k), 1), ((k,j,i), -1), ((k,i,j), -1)]:
        value[term] += sign
    return value


def audit():
    triples_checked = 0
    for rank in range(1, 9):
        blocks = defaultdict(list)
        for j,i,k in hall_triples(rank):
            blocks[tuple(sorted((i,j,k)))].append(tensor_bracket(j,i,k))
            triples_checked += 1
        assert sum(map(len, blocks.values())) == (rank**3-rank)//3
        for letters, block in blocks.items():
            words = sorted(set(permutations(letters)))
            rows = [[item[w] for w in words] for item in block]
            diag, _, height = diagonalize(rows, 0, len(words))
            assert height == len(block) and all(abs(diag[i][i]) == 1 for i in range(height))
            for j,i,k in words:
                assert not any(quotient(rows, [tensor_bracket(j,i,k)[w] for w in words]))
    shape = [2,1,0]
    triple = '[[a2,a1],a1]'
    mixed = '[a1,b1]'
    assert read(dict(spheres=shape, face={triple: 1})) == dict(raw=False, binary=None, joined=True)
    assert read(dict(spheres=shape, face={mixed: 1})) == dict(raw=False, binary=False, joined=False)
    relation = {triple: 1, mixed: -1}
    assert read(dict(spheres=shape, relations=[relation], face={mixed: 1}))['joined']
    case = dict(spheres=[1,1,0], relations=[{'a1.eta2.eta3': 1}],
                rules=[{'b1.eta3': 1, mixed: 2}], face={mixed: 2}, counts=[1])
    assert read(case) == dict(raw=False, binary=False, joined=True)
    case['face']['b1.eta3'] = 1
    assert read(case) == dict(raw=True, binary=True, joined=True)
    return triples_checked


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path, help='JSON with spheres, face and optional relations, rules and counts')
    parser.add_argument('--basis', type=int, nargs=3, metavar=('TWOS', 'THREES', 'FOURS'))
    args = parser.parse_args()
    if args.basis:
        for name, order, bottom in basis(*args.basis):
            print(f'{name}: order {order or "infinite"}; bottom wedge {bottom}')
    elif args.input:
        try:
            print(json.dumps(read(json.loads(args.input.read_text()))))
        except ValueError as error:
            parser.error(str(error))
    else:
        print(f'Checked {audit()} integral Hall triples through eight bottom spheres and the surface comparisons.')
