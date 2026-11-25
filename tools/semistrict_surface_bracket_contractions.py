"""Degree-six bracket membership with finite first-Hopf image after passing to
a cover fixing that image. Each color is [coefficient_order, subgroup_words].
Zero coefficient order or zero input order denotes no order bound. A packet
[n, vectors] allows all n-torsion differences within a color and precisely
the listed aggregate generators (in the direct sum of the color coefficients).
A family [k, packet1, packet2] contributes k times their bracket span.
A bracket row has terms [left_word, left_color, right_word, right_color, c].
JSON keys: deck_rank, colors, families, relations, face.
"""
from argparse import ArgumentParser
from collections import defaultdict, deque
from itertools import combinations, product
from math import gcd, lcm
from pathlib import Path
import json

from semistrict_surface_bracket_cosets import accepted, core, double_cosets, inv, certificate, presentation
from semistrict_surface_free_module_kernels import Lattice, analyze
from semistrict_surface_free_tree_placements import reduced


def scale(order, bound):
    if not bound:
        return 1
    return order//gcd(order, bound) if order else 0


def collect(terms):
    sums = defaultdict(int)
    for w, i, c in terms:
        sums[tuple(w), i] += c
    return [(w,i,c) for (w,i),c in sorted(sums.items()) if c]


class BracketCoordinates:
    def __init__(self, deck_rank, colors):
        self.rank = deck_rank
        self.colors = colors
        self.graphs = [core(H,deck_rank) for _, H in colors]
        self.orbits = []

    def factor(self, i, j, r, w):
        # Membership in H_i r H_j has already been certified.
        todo = deque([()])
        seen = {()}
        gens = [tuple(k) for k in self.colors[i][1]]
        while todo:
            h = todo.popleft()
            tail = reduced(inv(r)+inv(h)+w, self.rank)
            if accepted(self.graphs[j],tail):
                return h
            for k in gens:
                for v in (k,inv(k)):
                    z = reduced(h+v,self.rank)
                    if z not in seen:
                        seen.add(z)
                        todo.append(z)
        raise AssertionError("certified factorization missing")

    def mixed(self, col):
        terms = []
        for g,i,h,j,c in col:
            if not c:
                continue
            g,h = reduced(g,self.rank), reduced(h,self.rank)
            if i>j:
                g,i,h,j,c = h,j,g,i,-c
            w = reduced(inv(g)+h,self.rank)
            if i==j and accepted(self.graphs[i],w):
                continue
            for index,(p,q,r,recognize) in enumerate(self.orbits):
                if (p,q)!=(i,j):
                    continue
                if recognize(w):
                    break
                if i==j and recognize(inv(w)):
                    w,g,c = inv(w),h,-c
                    break
            else:
                index, r = len(self.orbits), w
                recognize = double_cosets(self.rank,self.colors[i][1],[r],self.colors[j][1])[0]
                self.orbits.append((i,j,r,recognize))
            k = self.factor(i,j,r,w)
            terms.append((reduced(g+k,self.rank),index,c))
        return collect(terms)


def compile_brackets(deck_rank, colors, families, relations, face):
    coords = BracketCoordinates(deck_rank,colors)
    n = len(colors)
    def tensor(i,j):
        return i*n+j
    def contract(col):
        return collect(term for g,i,h,j,c in col for term in [(g,tensor(i,j),c),(h,tensor(j,i),-c)])
    def valid(packet):
        bound, vecs = packet
        if bound<0 or any(len(v)!=n for v in vecs):
            raise ValueError("invalid aggregate packet")
        for v in vecs:
            for (order,_), x in zip(colors,v):
                if bound and (x*bound%order if order else x):
                    raise ValueError("aggregate generator violates its order bound")
    aggregate = []
    for k,left,right in families:
        valid(left)
        valid(right)
        for u,v in product(left[1],right[1]):
            aggregate.append(contract([((),i,(),j,k*a*b) for i,a in enumerate(u)
                                       for j,b in enumerate(v) if a and b]))
        for (bound,_),(_,vectors) in ((left,right),(right,left)):
            for i,(order,_) in enumerate(colors):
                t = k*scale(order,bound)
                for v in vectors:
                    for letter in range(1,deck_rank+1):
                        aggregate.append(collect(term for j,b in enumerate(v) if b
                                                 for term in [((letter,),tensor(i,j),t*b),
                                                              ((),tensor(i,j),-t*b)]))
    for i,(ni,H) in enumerate(colors):
        for j,(nj,_) in enumerate(colors):
            idx = tensor(i,j)
            mod = gcd(ni,nj)
            if mod:
                aggregate.append([((),idx,mod)])
            aggregate.extend([[(h,idx,1),((),idx,-1)] for h in H])
    cols = [coords.mixed(col) for col in [*relations,face]]
    mixed_rows = []
    for index,(i,j,r,_) in enumerate(coords.orbits):
        ni,Hi = colors[i]
        nj,Hj = colors[j]
        order = gcd(ni,nj)
        for k,(s,_),(t,_) in families:
            order = gcd(order,k*scale(ni,s)*scale(nj,t),k*scale(ni,t)*scale(nj,s))
        info = certificate(deck_rank,Hi,Hj,[r],same_color=i==j)["orbits"]
        for row in presentation(info,order):
            mixed_rows.append([(w,index,c) for w,_,c in row])
    off = len(coords.orbits)
    def shift(col):
        return [(w,i+off,c) for w,i,c in col]
    lifted = [a+shift(contract(col)) for a,col in zip(cols,[*relations,face],strict=True)]
    return dict(deck_rank=deck_rank,rank=off+n*n,relations=mixed_rows+[shift(r) for r in aggregate if r],
                steps=lifted[:-1],face=lifted[-1])


def decision(**spec):
    result = analyze(**compile_brackets(**spec))
    return result["coordinates"] is not None


def finite_oracle(lengths,colors,families,relations):
    # Explicit exterior group on all positions, with no deck variables.
    sites = [(i,x) for i,l in enumerate(lengths) for x in range(l)]
    pairs = list(combinations(sites,2))
    index = {key:j for j,key in enumerate(pairs)}
    width = len(pairs)
    rows = []
    for j,((i,_),(k,_)) in enumerate(pairs):
        order = gcd(colors[i][0],colors[k][0])
        if order:
            rows.append([int(q==j)*order for q in range(width)])
    def read(col,shift):
        out = [0]*width
        def site(w,i):
            return i,(sum(w)+shift)%lengths[i]
        for g,i,h,k,c in col:
            x,y = site(g,i),site(h,k)
            if x!=y:
                out[index[tuple(sorted((x,y)))]] += c if x<y else -c
        return out
    def gen(packet):
        b, vs = packet
        basis = []
        for i, (order,_) in enumerate(colors):
            for x in range(1,lengths[i]):
                m = scale(order,b)
                basis.append([((1,)*x,i,m),((),i,-m)])
        return basis+[[((),i,a) for i,a in enumerate(v)] for v in vs]
    for k,p,q in families:
        for u,v in product(gen(p),gen(q)):
            rows.append(read([(g,i,h,j,k*a*b) for g,i,a in u for h,j,b in v],0))
    rows.extend(read(row,s) for row in relations for s in range(lcm(*lengths)))
    lattice = Lattice(rows,width)
    return lambda col: lattice.coords(read(col,0)) is not None


def audit():
    configs = [
        ([3],[2],[[1,[0,[]],[0,[]]]]),
        ([2,2],[4,2],[[2,[0,[[1,1]]],[0,[]]],[1,[2,[[2,0]]],[2,[[2,1]]]]]),
        ([2,1],[0,4],[[2,[0,[[2,1]]],[0,[[1,0]]]],[1,[4,[[0,2]]],[0,[]]]]),
    ]
    count = 0
    for lengths,orders,families in configs:
        colors = [(o,[(1,)*l]) for l,o in zip(lengths,orders)]
        sites = [(i,(1,)*x) for i,l in enumerate(lengths) for x in range(l)]
        edges = [[(w,i,v,j,1)] for (i,w),(j,v) in combinations(sites,2)]
        for rels in ([],[edges[0]+edges[-1]]):
            oracle = finite_oracle(lengths,colors,families,rels)
            for e,f in product(edges,repeat=2):
                for face in (e,e+f):
                    assert decision(deck_rank=1,colors=colors,families=families,relations=rels,face=face)==oracle(face)
                    count += 1
    # Constant nonzero Hopf value on a free orbit. The null-input
    # bracket subgroup consists exactly of finite even-valence edge chains.
    def edge(g,h):
        return [(g,0,h,0,1)]
    e = edge((),(1,)); f = edge((1,),(2,)); g = edge((2,),())
    case = dict(deck_rank=2,colors=[(2,[])],families=[[1,[0,[]],[0,[]]]])
    assert decision(**case,relations=[],face=e+f+g)
    assert not decision(**case,relations=[],face=e)
    assert decision(**case,relations=[e],face=edge((2,),(2,1)))
    assert not decision(**case,relations=[e],face=edge((),(2,)))
    print(f"{count} signed exterior-lattice comparisons; free-deck triangle, single-edge and"
          " two translated attachment queries passed")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("input",nargs="?",type=Path)
    parser.add_argument("--compile",action="store_true",help="emit integral simultaneous span problem")
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        print(json.dumps(compile_brackets(**data) if args.compile else {"member":decision(**data)}))
    else:
        audit()
