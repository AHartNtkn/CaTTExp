"""Test degree-five bottom differences by substitutions into the pair Hopf tester.

JSON input: rank = dimension of A/2; forms = independent quadrics, one
nonnegative mask per middle character, low bits first in lexicographic pairs
(including diagonals). Optional face is a mask in eta, t_1, ..., t_rank blocks,
with one bit per middle coordinate in each block.
"""
import json
from argparse import ArgumentParser
from itertools import combinations, combinations_with_replacement
from pathlib import Path

from semistrict_surface_four_complex_operations import solve
from semistrict_surface_lens_squares import row_reduce
from semistrict_surface_pair_hopf import factor


def analyze(rank, forms, face=None):
    if type(rank) is not int or rank < 0:
        raise ValueError('rank must be a nonnegative integer')
    pairs = list(combinations_with_replacement(range(rank), 2))
    if any(type(f) is not int or not 0 < f < 1 << len(pairs) for f in forms):
        raise ValueError('each form must be a nonzero quadratic coefficient mask')
    if len(row_reduce(forms)) != len(forms):
        raise ValueError('the supplied quadratic forms must be independent')
    size = len(forms)
    width = (rank+1)*size
    if face is not None and (type(face) is not int or not 0 <= face < 1 << width):
        raise ValueError('face outside the eta and bracket coordinates')
    cubics = list(combinations_with_replacement(range(rank), 3))
    index = {monomial:i for i,monomial in enumerate(cubics)}
    equations = [0]*len(cubics)
    for s, form in enumerate(forms):
        for v,(i,j) in enumerate(pairs):
            if not form >> v & 1:
                continue
            for k in range(rank):
                equations[index[tuple(sorted((i,j,k)))]] ^= 1 << ((k+1)*size+s)
            if i != j:
                for monomial in ((i,i,j),(i,j,j)):
                    equations[index[monomial]] ^= 1 << s
    relations = row_reduce(equations)
    readings = []
    for gamma in range(1,1 << size):
        form = 0
        for s, value in enumerate(forms):
            if gamma >> s & 1:
                form ^= value
        factors = factor(rank, [form >> j & 1 for j in range(len(pairs))])
        if factors is None:
            continue
        l,m = factors
        character = gamma
        for k in range(rank):
            if (l^m) >> k & 1:
                character |= gamma << ((k+1)*size)
        assert all((r & character).bit_count() % 2 == 0 for r in equations)
        readings.append(dict(gamma=gamma, bottom_axes=[l,m], character=character))
    image_rank = len(row_reduce(r['character'] for r in readings))
    dim = width-len(relations)
    result = dict(bottom_dimension=dim, tester_rank=image_rank,
                  undetected_dimension=dim-image_rank, readings=readings)
    if face is not None:
        result['raw_nonzero'] = len(row_reduce([*relations.values(),face])) != len(relations)
        result['detecting_axes'] = [r['bottom_axes'] for r in readings
                                    if (face & r['character']).bit_count() % 2]
    return result


def check():
    # Enumerate unordered planes once. Independently calculate the group order
    # using integral elimination on the supplied bottom/middle groups.
    total = 0
    for r in (2,3):
        pairs = list(combinations_with_replacement(range(r),2))
        for f,g in combinations(range(1,1 << len(pairs)),2):
            if g > f^g:
                continue
            result = analyze(r,[f,g])
            assert result['undetected_dimension'] == 0
            q = [[(v >> j) & 1 for v in (f,g)] for j in range(len(pairs))]
            orders = solve([2]*r,[2,2],q)['bottom_image']
            assert all(n == 2 for n in orders) and len(orders) == result['tester_rank']
            total += 1
    # Common factor, with a pure cubic which vanishes in the two basis readings.
    # Bits in x^2, xy, xz, y^2, yz, z^2 order.
    shared = analyze(3,[2,4],1 << 6)
    assert shared['raw_nonzero'] and shared['tester_rank'] == 3
    assert shared['detecting_axes'] in ([[1,6]], [[6,1]])
    # Three minors of two independent rows, ordered by omitted column.
    pairs = list(combinations_with_replacement(range(6),2))
    minors = [sum(1 << pairs.index((a,3+b)) for a,b in ((i,j),(j,i)))
              for i,j in ((1,2),(0,2),(0,1))]
    face = 1 << 3  # bracket of the first minor with the first row's first letter
    net = analyze(6,minors,face)
    assert net['raw_nonzero'] and net['bottom_dimension'] == 2 and not net['readings']
    q = [[f >> i & 1 for f in minors] for i in range(len(pairs))]
    assert solve([2]*6,[2]*3,q)['bottom_image'] == [2,2]
    return total, minors


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path)
    args = parser.parse_args()
    if args.input:
        try:
            print(json.dumps(analyze(**json.loads(args.input.read_text()))))
        except (KeyError, TypeError, ValueError) as error:
            parser.error(str(error))
    else:
        count, minors = check()
        print(f'{count} distinct quadratic pencils checked against integral groups. '
              f'Three-minor example {minors} has two undetected dimensions.')
