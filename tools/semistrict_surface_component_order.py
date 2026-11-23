"""Decide directed degree-four attachments on virtually abelian history groups.

Accepts --presentation JSON in the semistrict_surface_history_group format.
Elsewhere a negative answer in the permutation/pair-crossing quotient is sound.
"""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_component_braids import Components
from semistrict_surface_history_group import Presentation
from semistrict_surface_penultimate_intervals import check as smt_check


class PairGroup:
    def __init__(self, n):
        self.pairs = list(combinations(range(n), 2))
        self.index = {x:i for i,x in enumerate(self.pairs)}
        self.one = tuple(range(n)), (0,)*len(self.pairs)

    def act(self, p, v):
        w = [0]*len(v)
        for a, (i,j) in zip(v, self.pairs):
            w[self.index[tuple(sorted((p[i],p[j])))]] = a
        return tuple(w)

    def mul(self, x, y):
        p, v = x
        q, w = y
        return tuple(p[i] for i in q), tuple(a+b for a,b in zip(v,self.act(p,w)))

    def inv(self, x):
        p, v = x
        q = tuple(p.index(i) for i in range(len(p)))
        return q, self.act(q,tuple(-a for a in v))

    def word(self, w):
        p, v = map(list,self.one)
        for g in w:
            i = abs(g)-1
            a,b = p[i:i+2]
            v[self.index[tuple(sorted((a,b)))]] += 1 if g>0 else -1
            p[i:i+2] = b,a
        return tuple(p),tuple(v)


def transversal(group, gens):
    reps = {group.one[0]: group.one}
    states = [group.one]
    lattice = set()
    for x in states:
        for g in gens:
            y = group.mul(x,g)
            ref = reps.get(y[0])
            if ref is None:
                states.append(y)
                reps[y[0]] = y
            else:
                p,v = group.mul(y,group.inv(ref))
                assert p == group.one[0]
                if any(v):
                    lattice.add(min(v, tuple(-a for a in v)))
    return reps, lattice


def sum_terms(terms):
    terms = list(terms)
    if len(terms) <= 1:
        return terms[0] if terms else '0'
    return '(+ '+' '.join(terms)+')'


def attainable(group, gens, defects, target):
    gens = set(gens)
    gens.update(group.inv(g) for g in tuple(gens))
    reps, lattice = transversal(group, gens)
    moves = set()
    for d in set(defects)-{group.one}:
        for t in reps.values():
            p,v = group.mul(group.mul(t,d),group.inv(t))
            if (p,v) not in moves:
                moves.add((p,v))
    zero = group.one[0]
    states, indices = [zero], {zero:0}
    edges = set()
    for i, r in enumerate(states):
        for p,v in moves:
            s = tuple(r[j] for j in p)
            if s not in indices:
                indices[s] = len(states)
                states.append(s)
            periods = set()
            for u in lattice:
                diff = tuple(a-b for a,b in zip(u,group.act(p,u)))
                if any(diff):
                    w = group.act(r,diff)
                    periods.add(min(w,tuple(-a for a in w)))
            edges.add((i,indices[s],group.act(r,v),tuple(sorted(periods))))
    info = dict(permutations=len(reps), states=len(states), transitions=len(edges))
    if target == group.one:
        return dict(info, accepted=True)
    if target[0] not in indices or not edges:
        return dict(info, accepted=False)
    end = indices[target[0]]
    lines = ['(set-logic QF_LIA)']
    def integer(name):
        lines.append(f'(declare-const {name} Int)')
        return name
    def require(condition):
        lines.append(f'(assert {condition})')
    ranks = [integer(f'h{i}') for i in range(len(states))]
    require(f'(= {ranks[0]} 0)')
    parents, used = defaultdict(list), defaultdict(set)
    incoming, outgoing = defaultdict(list), defaultdict(list)
    coords = [[] for _ in target[1]]
    def accumulate(w,var):
        for col,k in zip(coords,w):
            if k:
                col.append(f'(* {k} {var})')
    for i,(s,t,v,periods) in enumerate(sorted(edges)):
        count = integer(f'c{i}')
        require(f'(>= {count} 0)')
        outgoing[s].append(count)
        incoming[t].append(count)
        used[s].add(count)
        used[t].add(count)
        if s != t:
            for a,b in ((s,t),(t,s)):
                parents[b].append(f'(and (> {count} 0) (< {ranks[a]} {ranks[b]}))')
        accumulate(v,count)
        for j,w in enumerate(periods):
            var = integer(f'z{i}_{j}')
            require(f'(=> (= {count} 0) (= {var} 0))')
            accumulate(w,var)
    for i in range(len(states)):
        require(f'(= (- {sum_terms(outgoing[i])} {sum_terms(incoming[i])}) {int(i==0)-int(i==end)})')
        if i:
            parent = '(or '+' '.join(parents[i])+')' if parents[i] else 'false'
            require(f'(=> (> {sum_terms(sorted(used[i]))} 0) {parent})')
    for terms,k in zip(coords,target[1]):
        require(f'(= {sum_terms(terms)} {k})')
    answer = smt_check('\n'.join(lines+['(check-sat)']))
    if answer not in ('sat','unsat'):
        raise RuntimeError(f'integer feasibility did not decide the order: {answer}')
    return dict(info, accepted=answer=='sat')


def solve(data):
    pres = Presentation(data)
    q = pres.query
    h = tuple((p,e) for e,(p,_) in enumerate(q.history))
    ports = {e:pres.marks[label] for e,(_,label) in enumerate(q.history)}
    faces = Components(h,ports,len(q.path)).faces
    exact = all(len(f)<=2 for f in faces)
    group = PairGroup(len(h))
    gs = {i:group.word(pres.braids[i]) for i in pres.generators}
    def interpret(w):
        v = group.one
        for g in w:
            a = gs[abs(g)]
            v = group.mul(v,a if g>0 else group.inv(a))
        return v
    result = attainable(group,gs.values(),map(interpret,pres.defects),interpret(pres.target))
    answer = result['accepted'] if exact or not result['accepted'] else None
    return dict(result, exact=exact, surface=answer, largest_sibling_family=max(map(len,faces),default=0))


def checks():
    from random import Random
    from semistrict_surface_component_braids import cabling, restrict
    from semistrict_surface_history_group import inv
    from semistrict_surface_shared_edge import braid_image
    rng = Random(168)
    # Two identical closed bigons, each with two indistinguishable marked
    # points. Their outer exchange swaps the two independent internal axes.
    h = [(0,'U'),(1,'s'),(1,'s'),(0,'D')]*2
    outer = cabling(((0,0,4),(1,4,8)),(1,))
    group = PairGroup(8)
    a, b, t = map(group.word,[(2,),(6,),outer])
    gs = (a,b,t)
    assert group.mul(t,a) == group.mul(b,t) and group.mul(t,a) != group.mul(a,t)
    def normal(x,y,k):
        w = (2 if x>=0 else -2,)*abs(x)+(6 if y>=0 else -6,)*abs(y)
        return group.word(w+(outer if k>=0 else inv(outer))*abs(k))
    checked = 0
    # Independent Z^2 semidirect Z orbit formula for a single directed rule.
    for u,v,k in ((0,0,1),(2,-1,1),(1,-2,-1),(1,2,2),(1,-1,0),(2,0,0)):
        d = normal(u,v,k)
        for _ in range(18):
            x,y,z = rng.randrange(-4,5),rng.randrange(-4,5),rng.randrange(-4,5)
            if rng.randrange(2):
                copies = rng.randrange(1,4)
                z = k*copies
                if k%2:
                    y = copies*(u+v)-x
                else:
                    c = rng.randrange(copies+1)
                    x,y = c*u+(copies-c)*v,c*v+(copies-c)*u
            if k:
                m = z//k
                expected = (x,y,z)==(0,0,0) or (z==m*k and m>0 and
                    (x+y==m*(u+v) if k%2 else any((x,y)==(j*u+(m-j)*v,j*v+(m-j)*u) for j in range(m+1))))
            else:
                from semistrict_surface_scalar_sites import coefficients
                expected = z==0 and coefficients([(u,v),(v,u)],(x,y)) is not None
            assert attainable(group,gs,[d],normal(x,y,z))['accepted'] == expected
            checked += 1
    def entry(l,r):
        return ['v','',h,l,r]
    base = dict(edges={'x':['v','v']},rules={'U':['v','','xx'],'D':['v','xx',''],'s':['v','','']})
    for l,r,rules,expected in [((),(6,),[((),(2,))],True),((6,),(),[((),(2,))],False),
                                ((),outer,[((),outer)],True),((2,),(6,),[((),outer)],False)]:
        d = dict(base,query=entry(l,r),attachments=[entry(a,b) for a,b in rules])
        p = Presentation(d)
        assert p.abelian_decision() is None
        answer = solve(d)
        assert answer['exact'] and answer['permutations']==8 and answer['surface']==expected
    # A missing cable strand kills a Brunnian word, even after conjugation
    # through arbitrary ambient braids, unequal widths and a stationary strand.
    face = ((0,1,2),(1,2,4),(2,4,7))
    a,b = (1,1),(2,2)
    w = a+b+inv(a)+inv(b)
    q = cabling(face,w)
    projections = hits = 0
    for _ in range(15):
        g = tuple(rng.choice((-1,1))*rng.randrange(1,7) for _ in range(7))
        order = list(range(7))
        for z in g:
            i=abs(z)-1
            order[i:i+2] = order[i:i+2][::-1]
        for triple in combinations(range(7),3):
            middle = {i for i,e in enumerate(order) if e in triple}
            keep = all(any(i<=e<j for e in middle) for _,i,j in face)
            c = restrict(7,g,set(triple))
            predicted = c+w+inv(c) if keep else ()
            actual = restrict(7,g+q+inv(g),set(triple))
            assert braid_image(3,actual)==braid_image(3,predicted)
            hits += keep
            projections += 1
    assert hits
    print(f'{checked} virtually abelian order queries agree with independent orbit formulas; '
          f'four positioned attachment decisions on a nonabelian eight-permutation component. '
          f'{projections} conjugated triple projections, {hits} retaining all three blocks.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--presentation',type=Path)
    args = parser.parse_args()
    if args.presentation:
        print(json.dumps(solve(json.loads(args.presentation.read_text()))))
    else:
        checks()
