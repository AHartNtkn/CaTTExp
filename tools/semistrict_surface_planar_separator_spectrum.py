"""Refine private planar degree bounds by splitting the spatial join graph.

--base FILE uses the positive planar paths and higher declarations of the
layer solver. The reported certificate is a tree of level bounds and cuts.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, permutations, product
import json
from pathlib import Path

from semistrict_surface_planar_layer_spectrum import optimize, presentation, profile
from semistrict_surface_tree_spectra import context_spectrum


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def separators(before, weights):
    n = len(weights)
    full = (1<<n)-1
    neighbors = [m|sum(1<<j for j in range(n) if before[j]&(1<<i)) for i,m in enumerate(before)]

    @cache
    def weight(mask):
        if not mask:
            return 0
        i = next(indices(mask))
        return max(weight(mask & ~(1<<i)), weights[i]+weight(mask & neighbors[i]))

    @cache
    def lower(mask):
        best = 0
        for a in indices(mask):
            for b in indices(mask & before[a]):
                above = sum(1<<j for j in indices(mask) if before[j]&(1<<a))
                best = max(best,2+weight(mask & before[b])+weight(above))
        return best

    @cache
    def split(mask):
        ids = list(indices(mask))
        local = [sum(1<<k for k,j in enumerate(ids) if before[i]&(1<<j)) for i in ids]
        costs = [weights[i] for i in ids]
        limit,layers = optimize(local,costs)
        cert = {'layers':[[ids[k] for k in g] for g in layers]}
        target = lower(mask)
        if all(w<=2 for w in costs):
            return target,{'private_height_at_most_two':ids}
        if limit==target:
            return limit,cert
        # For each common set, only a partition of its exterior into entire
        # connected components is admissible. All binary splits are covered.
        common = mask
        while common:
            common = (common-1)&mask
            if weight(common)>=limit:
                continue
            free = mask ^ common
            connected = []
            while free:
                todo = free & -free
                component = 0
                while todo:
                    component |= todo
                    adj = 0
                    for i in indices(todo):
                        adj |= neighbors[i]
                    todo = free & adj & ~component
                free ^= component
                connected.append(component)
            for choice in range(1,1<<(len(connected)-1)):
                left = sum(g for i,g in enumerate(connected) if choice&(1<<i))
                right = mask ^ common ^ left
                l,lc = split(common|left)
                if l>=limit:
                    continue
                r,rc = split(common|right)
                bound = max(l,r,weight(common))
                if bound<limit:
                    limit,cert = bound,dict(common=list(indices(common)),shared_rank=weight(common),
                                            left=lc,right=rc)
                    if limit==target:
                        return limit,cert
        return limit,cert
    value,tree = split(full)
    return lower(full),value,tree


def solve(data):
    slots,heights,arrows,before = presentation(data)
    base = context_spectrum(dict(edges=arrows,slots=[(*s,heights[s]) for s in slots]))
    if 'failing_from' in base:
        return base
    low,high,tree = separators(before,[heights[s] for s in slots])
    assert base['failing_degrees']==list(range(3,low+2))
    return {**base,'undecided_by_bounds':list(range(max(3,low+2),high+2)),
            'slots':slots,'certificate':tree}


def check_fibres():
    # Independent enumerations of the admissible cuts of two projected lists
    # test their joint injectivity, including shared cells in low degrees.
    cases = forests = exclusive = 0
    n = 5
    for other in permutations(range(n)):
        before = [sum(1<<j for j in range(i) if other.index(j)<other.index(i)) for i in range(n)]
        def valid(word,ids):
            return all(not(before[i]&(1<<j)) or word[i]==0 or word[j]==2 for i in ids for j in ids)
        all_ids = tuple(range(n))
        words = [w for w in product(range(3),repeat=n) if valid(w,all_ids)]
        for a,b in combinations(range(n),2):
            if not before[b]&(1<<a):
                continue
            left = tuple(i for i in all_ids if i!=b)
            right = tuple(i for i in all_ids if i!=a)
            fibres = defaultdict(list)
            only = (Counter(),Counter())
            for w in words:
                l,r = tuple(w[i] for i in left),tuple(w[i] for i in right)
                if w[a]==1:
                    only[0][l]+=1
                elif w[b]==1:
                    only[1][r]+=1
                else:
                    fibres[tuple(w[i] for i in all_ids if i not in (a,b))].append((l,r))
            for count,ids,idx in zip(only,(left,right),(a,b)):
                expected = {tuple(w[i] for i in ids) for w in product(range(3),repeat=n)
                            if w[idx]==1 and valid(w,ids)}
                assert set(count)==expected and all(m==1 for m in count.values())
                exclusive += len(expected)
            for pairs in fibres.values():
                # An integer row on the edges has injective vertex sums iff this
                # bipartite graph is a forest. Detect cycles by edge insertion.
                parent = {}
                def root(x):
                    while x in parent:
                        x = parent[x]
                    return x
                for l,r in pairs:
                    u,v = root((0,l)),root((1,r))
                    assert u!=v
                    parent[u]=v
                forests+=1
            cases+=1
    return cases,forests,exclusive


def check_pastes():
    from semistrict_surface_globular_judgment import facets,tensor_rows
    from semistrict_surface_tree_spectra import Tree
    trees = [Tree([[[]]]),Tree([[[]]]),Tree([[]]),Tree([[[]]]),Tree([[[]]])]
    left,right = (0,1,2),(2,3,4)
    def differential(row):
        out = Counter()
        for word,m in row.items():
            for face,s in facets(trees,word):
                out[face] += s*m
        return {w:v for w,v in out.items() if v}
    def admissible(w):
        return all(w[i]==(0,1) or w[j]==(0,0) for i in (0,1) for j in (3,4))
    comparisons = 0
    for k in (2,3,4):
        side = [[],[]]
        for w in tensor_rows(trees,k+1):
            if admissible(w):
                side[int(any(w[i][0] for i in (3,4)))].append(w)
        maps = [{},{}]
        for w in tensor_rows(trees,k):
            if admissible(w):
                j = int(any(w[i][0] for i in (3,4)))
                key = tuple(w[i] for i in (left,right)[j])
                assert key not in maps[j]
                maps[j][key] = w
        for a,b in product(*side):
            original,adjusted = Counter(),Counter()
            for j,w in enumerate((a,b)):
                for f,sgn in facets(trees,w):
                    if sgn<0:
                        original[f]+=1
                    else:
                        key = tuple(f[i] for i in (left,right)[j])
                        adjusted[maps[j][key]]+=1
            assert differential(original)==differential(adjusted)
            comparisons+=1
    return comparisons


def checks():
    cases,forests,exclusive = check_fibres()
    pastes = check_pastes()
    for h in (3,7,15):
        lo,hi,tree = separators([0,1,3,7,1],[1,1,1,1,h])
        assert (lo,hi)==(4,4) and 'common' in tree
    assert separators([0,1,3,7],[2,3,4,5])[:2]==(profile([2,3,4,5]),)*2
    # A realizable slot order where even all recursive cuts leave a gap.
    mixed = [0,0,3,2,0,17,15,95]
    assert separators(mixed,[50,10,10,50,10,50,50,10])[:2]==(62,70)
    print(f'{cases} interval splits, {forests} shared-cut forests, {exclusive} unique exclusive '
          f'lifts, {pastes} alternate decorated hemisphere pastes; tall overlapping rule resolved')


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('--base',type=Path)
    args = p.parse_args()
    if args.base:
        print(json.dumps(solve(json.loads(args.base.read_text()))))
    else:
        checks()
