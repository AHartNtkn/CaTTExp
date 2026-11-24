"""Detect higher configuration spheres given as sums of iterated meridian brackets.

JSON fields: holes, meridians (pairs [fixed particle, signed hole word]), terms
(pairs [coefficient, tree]). A tree is a zero-based meridian index or [left,right].
Signs use the Samelson bracket on the adjoints. The output is a certificate
when the integral loop-homology image is nonzero.
"""
from argparse import ArgumentParser
from collections import Counter
import json
from pathlib import Path

from semistrict_surface_gap_linking import brunnian, cover, lift
from semistrict_surface_history_group import reduced


def nonzero(coefficients):
    return {key: value for key, value in coefficients.items() if value}


def evaluate(tree, letters):
    if type(tree) is int and 0 <= tree < len(letters):
        letter = letters[tree]
        return 1, {} if letter is None else {(letter,): 1}
    if not isinstance(tree, list) or len(tree) != 2:
        raise ValueError('a bracket needs two children or a valid meridian index')
    p, left = evaluate(tree[0], letters)
    q, right = evaluate(tree[1], letters)
    values = Counter()
    sign = (-1)**(p*q)
    for a, x in left.items():
        for b, y in right.items():
            values[a+b] += x*y
            values[b+a] -= sign*x*y
    return p+q, nonzero(values)


def polynomial(terms, letters):
    weight = None
    values = Counter()
    for coefficient, tree in terms:
        if type(coefficient) is not int:
            raise ValueError('a coefficient must be an integer')
        degree, value = evaluate(tree, letters)
        if weight is not None and degree != weight:
            raise ValueError('all terms must have the same bracket weight')
        weight = degree
        for word, n in value.items():
            values[word] += coefficient*n
    return weight, nonzero(values)


def certificate(data):
    holes = data['holes']
    if type(holes) is not int or holes < 0:
        raise ValueError('holes must be a nonnegative integer')
    letters = []
    for particle, word in data['meridians']:
        if type(particle) is not int or particle < 0:
            raise ValueError('expected a nonnegative fixed-particle index')
        if any(type(x) is not int or not 1 <= abs(x) <= holes for x in word):
            raise ValueError('expected a word in the signed hole generators')
        letters.append((particle, reduced(word)))
    terms = data['terms']
    weight, value = polynomial(terms, letters)
    if not value:
        return {'loop_homology_detected': False}

    # Also separate input letters cancelled in the source; independently
    # evaluate the initial expression after choosing actual lifts in the cover.
    sheets, permutations = cover([word for _, word in letters], holes)
    lifted = [(particle, lift(word, 0, permutations)) for particle, word in letters]
    assert len(set(letters)) == len(set(lifted))
    witness = min(value, key=lambda w: (len(set(w)), w))
    addresses = dict(zip(letters, lifted, strict=True))
    target = tuple(addresses[a] for a in witness)
    keep = set(target)
    _, reading = polynomial(terms, [a if a in keep else None for a in lifted])
    assert reading[target] == value[witness]
    return {'loop_homology_detected': True, 'homotopy_degree': weight+1,
            'sheets': len(sheets), 'hole_permutations': permutations,
            'moving_sheet': 0, 'fixed_lifts': sorted(keep),
            'tensor_word': target, 'coefficient': reading[target]}


def nested(indices):
    tree = indices[0]
    for index in indices[1:]:
        tree = [tree, index]
    return tree


def audit():
    for k in range(2, 10):
        m = k-1
        for holes in range(1, 6):
            twist = brunnian(holes)
            meridians = [(i, ()) for i in range(m)] + [(0, twist)]
            terms = [(1, nested(list(range(m)))), (-1, nested([m, *range(1, m)]))]
            data = dict(holes=holes, meridians=meridians, terms=terms)
            result = certificate(data)
            assert result['homotopy_degree'] == k and len(result['fixed_lifts']) == m
            for h in range(1, holes+1):
                restricted = [(i, [x for x in w if abs(x) != h]) for i,w in meridians]
                assert not certificate(dict(data, meridians=restricted))['loop_homology_detected']
            for missing in range(m):
                assert not polynomial(terms, [None if i == missing else (i,w)
                                              for i,w in meridians])[1]
        print(f'pi_{k}: detected on {k} lifted points for 1 through 5 holes; '
              f'all fixed-particle and single-hole omissions vanish')
    assert polynomial([(1,[0,0])], ['x'])[1] == {('x','x'): 2}
    jacobi = [(1,[0,[1,2]]), (1,[1,[2,0]]), (1,[2,[0,1]])]
    assert not polynomial(jacobi, list('xyz'))[1]
    # The two signed paths are equal after free reduction.
    data = dict(holes=2, meridians=[(0,[2,-1,1]),(0,[2])], terms=[(1,0),(-1,1)])
    assert not certificate(data)['loop_homology_detected']


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, nargs='?')
    args = parser.parse_args()
    if args.input:
        print(json.dumps(certificate(json.loads(args.input.read_text())), indent=2))
    else:
        audit()
