"""Decide raw Gray inhabitation from evaluated parallel faces on a common positional shape.

For --judgment FILE give global 'degree' >= 2 and 'columns', the ordered child
trees of the common ordinary boundary shape (a tree is a list of children).
'slots' is the ordered list of [source name,target name] at all local
(degree-2)-positions, by column then tree order. 'moves' lists pairs of names
of (degree-1)-generators joined by a generating degree-cell. Lower positional
labels must already agree. 'source' and 'target' are the top chains of the
two parallel old faces in their respective copies of the positional tree.
Use [word,positive multiplicity] entries, a word listing [rank,index] in each
column, with zero-based indices in recursive tree order at that rank. An empty
spine uses the empty tensor. Inputs are evaluated old judgments, not raw syntax.
"""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from itertools import product
import json
from pathlib import Path

from semistrict_surface_penultimate_intervals import check, total
from semistrict_surface_tree_spectra import Tree


def tensor_rows(trees, rank):
    def visit(i, remaining, prefix):
        if i == len(trees):
            if remaining == 0:
                yield tuple(prefix)
            return
        for d, cells in trees[i].layers.items():
            if d <= remaining:
                for x in cells:
                    yield from visit(i+1, remaining-d, [*prefix, (d,x)])
    return list(visit(0,rank,[]))


def facets(trees, word):
    sign = 1
    for i, (d,x) in enumerate(word):
        if d:
            lo, hi = trees[i].faces[x]
            for f, n in ((lo,-sign),(hi,sign)):
                yield word[:i]+((d-1,f),)+word[i+1:], n
        sign *= (-1)**d


def feasible(trees, degree, delta):
    rows = defaultdict(list)
    lines = ['(set-logic QF_LIA)']
    for j, word in enumerate(tensor_rows(trees,degree)):
        var = f'x{j}'
        lines.extend((f'(declare-const {var} Int)',f'(assert (>= {var} 0))'))
        for face, sign in facets(trees,word):
            rows[face].append(var if sign==1 else f'(- {var})')
    for f in rows.keys() | delta.keys():
        lines.append(f'(assert (= {total(rows[f])} {delta.get(f,0)}))')
    status = check('\n'.join([*lines,'(check-sat)']))
    if status not in ('sat','unsat'):
        raise RuntimeError(status)
    return status=='sat'


def reaches(edges, start, end):
    seen = {start}
    stack = [start]
    while stack:
        a = stack.pop()
        if a==end:
            return True
        for b in edges[a]-seen:
            seen.add(b)
            stack.append(b)
    return False


def decide(data):
    r = data['degree']-2
    trees = [Tree(t) for t in data['columns']]
    if r < 0 or any(t.height>r for t in trees):
        raise ValueError('boundary shape exceeds the boundary degree')
    if len(data['slots']) != sum(len(t.layers.get(r,[])) for t in trees):
        raise ValueError('expected a label pair for each top-dimensional position')
    edges = defaultdict(set)
    for a,b in data['moves']:
        edges[a].add(b)
    def decode(entries):
        row = Counter()
        for w,n in entries:
            if len(w)!=len(trees) or sum(d for d,_ in w)!=r or type(n)!=int or n<=0:
                raise ValueError('invalid face chain degree or multiplicity')
            if any(d<0 or j<0 or j>=len(t.layers.get(d,())) for t,(d,j) in zip(trees,w)):
                raise ValueError('basis index out of bounds')
            row[tuple((d,t.layers[d][j]) for t,(d,j) in zip(trees,w))] += n
        return row
    delta = decode(data['target'])
    delta.subtract(decode(data['source']))
    return all(reaches(edges,a,b) for a,b in data['slots']) and feasible(trees,r+1,delta)


def checks():
    # Independently expand actual label paths to spatial tensor charts and
    # compare on paths interleaving one distinguished event and other events.
    from itertools import permutations
    count = 0
    for width in range(1,4):
        orders = list(permutations(range(width)))
        for length in range(4):
            names = list(range(length+1))
            moves = list(zip(names,names[1:]))
            trees = [Tree([[[] for _ in range(length)]])]+[Tree([[]]) for _ in range(width-1)]
            def path(order, phase):
                bits = [0]*width
                result = []
                for i in order:
                    w = [(0,j) for j in bits]
                    w[i] = (1,phase if i==0 else 0)
                    result.append((w,1))
                    bits[i] = 1
                return result
            for s,t in product(orders,repeat=2):
                data = {'degree':3,'columns':[[[]]]*width,
                        'slots':[(0,length)]+[(0,0)]*(width-1),'moves':moves,
                        'source':path(s,0),'target':path(t,0)}
                delta = Counter()
                for reading,sign in ((path(s,0),-1),(path(t,length),1)):
                    for w,n in reading:
                        delta[tuple((d,tr.layers[d][j]) for tr,(d,j) in zip(trees,w))]+=sign*n
                assert decide(data)==feasible(trees,2,delta)
                count += 1
    for n in range(2,9):
        line = []
        for _ in range(n-2):
            line = [line]
        def atom(rank):
            return [[[(rank,0)],1]]
        data = {'degree':n,'columns':[line],'slots':[(0,2)],'moves':[(0,1),(1,0),(1,2)],
                'source':atom(n-2),'target':atom(n-2)}
        assert decide(data)
        data['slots'] = [(2,0)]
        assert not decide(data)
    # A degree-six directed boundary in the exceptional three-column family.
    trees = [Tree([[[]]]),Tree([[[[]]]]),Tree([[[]]])]
    for w in tensor_rows(trees,5):
        sides = [[],[]]
        for face,sign in facets(trees,w):
            encoded = [(d,t.layers[d].index(x)) for t,(d,x) in zip(trees,face)]
            sides[int(sign>0)].append([encoded,1])
        data = {'degree':6,'columns':[[[[]]],[[[[]]]],[[[]]]],'slots':[],'moves':[],
                'source':sides[0],'target':sides[1]}
        assert decide(data)
        data['source'],data['target'] = data['target'],data['source']
        assert not decide(data)
    print(f'{count} expanded-path comparisons, cyclic label checks in degrees 2–8, '
          f'and both directions of {len(tensor_rows(trees,5))} degree-six atoms verified')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--judgment',type=Path)
    args = parser.parse_args()
    if args.judgment:
        print(json.dumps({'raw_filler':decide(json.loads(args.judgment.read_text()))}))
    else:
        checks()
