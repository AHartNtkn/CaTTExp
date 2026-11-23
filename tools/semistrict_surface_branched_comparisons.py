"""Check the degree-six square quotient on three branching positional columns.

--trees takes a JSON list of the three trees. A tree is a list of children.
The middle height is three or four, and the outer heights are both two.
Use --emit FILE to export a quantified integer query. A positive answer gives
a quotient-only comparison, not a converted term.
"""

from argparse import ArgumentParser
from collections import Counter
from copy import deepcopy
from itertools import pairwise
import json
from pathlib import Path

from semistrict_surface_globular_judgment import Tree, facets, tensor_rows
from semistrict_surface_globe_spectrum import check, tableau_query


def query(shapes):
    trees = [Tree(s) for s in shapes]
    if [t.height for t in trees] not in ([2,3,2],[2,4,2]):
        raise ValueError('expected local column heights (2,3,2) or (2,4,2)')
    layers = [tensor_rows(trees,r) for r in range(6)]
    return tableau_query(layers,5,lambda word:facets(trees,word))


def survives(word):
    return all((a,b)!=(1,1) for a,b in pairwise(d for d,_ in word if d))


def certificate_rows():
    return [
        ([0],[7]),
        ([0,5,23],[13,18,24]),
        ([0,3,8,12,35,40,52],[17,22,27,31,42,47,55]),
        ([0,3,7,12,14,31,36,41,45,62,67],[17,21,25,26,28,46,49,54,58,65,70]),
        ([1,2,4,7,18,22,26,27,44,46,49,54,60],[9,10,12,15,28,31,34,38,45,47,52,55,61])]


def certificate():
    # Basis order is the tree order of tensor_rows. The two sides of each
    # lower tableau row are given together, independently of any solver.
    trees = [Tree(s) for s in [[[[]]],[[[[]],[[]]]],[[[]]]]]
    basis = [tensor_rows(trees,r) for r in range(6)]
    rows = certificate_rows()
    def diff(rank,indices):
        out = Counter()
        for i in indices:
            for f,n in facets(trees,basis[rank][i]):
                out[f] += n
        return out
    delta = Counter()
    for r,(src,tgt) in enumerate(rows):
        for row in (src,tgt):
            if r==0:
                assert len(row)==1
            else:
                assert diff(r,row)==delta
        delta = Counter(basis[r][i] for i in tgt)
        delta.subtract(basis[r][i] for i in src)
    top = [5,8,14,19,21,23,30]
    error = diff(5,top)
    error.subtract(delta)
    assert any(error.values()) and all(not survives(w) for w,c in error.items() if c)
    weights = dict.fromkeys([2,3,5,10,17,21,24,28,29],-1) | {1:1,9:1}
    functional = {basis[4][i]:n for i,n in weights.items()}
    def score(chain):
        return sum(n*functional.get(w,0) for w,n in chain.items())
    assert all(score(diff(5,[i]))>=0 for i in range(len(basis[5])))
    assert score(delta)<0

    # Replay a positive firing order on all surviving degree-four coordinates.
    remaining = [5,8,14,19,21,23,30]
    marking = Counter(basis[4][i] for i in rows[-1][0] if survives(basis[4][i]))
    for j in [0,0,2,2,2,1,0]:
        atom = remaining.pop(j)
        for f,n in facets(trees,basis[5][atom]):
            if survives(f):
                marking[f] += n
                assert marking[f]>=0
    assert marking==Counter(basis[4][i] for i in rows[-1][1] if survives(basis[4][i]))
    print(f'Certified two parallel old faces, seven quotient atoms and a raw separating '
          f'functional of value {score(delta)} on the face difference.')


def elementary():
    for axis,height in enumerate((2,3,2)):
        for depth in range(height):
            trees = [[[[]]],[[[[]]]],[[[]]]]
            node = trees[axis]
            for _ in range(depth):
                node = node[0]
            node.append(deepcopy(node[0]))
            answer = check(query(trees))
            print(f'column {axis+1}, depth {depth}: {answer}',flush=True)
            assert answer==('sat' if (axis,depth)==(1,1) else 'unsat')


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('--trees',type=json.loads)
    p.add_argument('--emit',type=Path)
    args = p.parse_args()
    if args.trees is not None or args.emit:
        formula = query(args.trees if args.trees is not None else [[[[]]],[[[[]],[[]]]],[[[]]]])
        if args.emit:
            args.emit.write_text(formula)
        else:
            print(check(formula))
    else:
        certificate()
        elementary()
