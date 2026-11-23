"""Decide pasting of a specified positive tableau in the generated square quotient.

By default reconstruct and independently replay all three quotient fillers at
the Response 117 boundary. --emit FILE writes their shared composition DAG.
"""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from functools import cache, lru_cache
from itertools import combinations_with_replacement, product
import json
from pathlib import Path

from gray_globe_comparison import atom
from semistrict_surface_branched_comparisons import certificate_rows, survives
from semistrict_surface_globular_judgment import Tree, facets, tensor_rows
from semistrict_surface_penultimate_intervals import check, total
from semistrict_surface_square_quotient_chains import Space


def vector(entries):
    result = []
    for i,n in sorted(entries.items()):
        if int(n)!=n:
            raise ValueError('expected an integral quotient normal form')
        if n:
            result.append((i,int(n)))
    return tuple(result)


@lru_cache(maxsize=32768)
def add(a,b):
    v = Counter(dict(a))
    v.update(dict(b))
    return vector(v)


@lru_cache(maxsize=32768)
def minus(a,b):
    v = Counter(dict(a))
    v.subtract(dict(b))
    return vector(v)


def mass(v):
    return sum(n for _,n in v)


class Chart:
    def __init__(self,shapes,rank):
        self.trees = [Tree(t) for t in shapes]
        self.layers = [tensor_rows(self.trees,r) for r in range(rank+2)]
        self.indices = [{w:i for i,w in enumerate(layer)} for layer in self.layers]
        relations = [Space() for layer in self.layers]
        def impose(space,relation):
            reduced = space.reduce(relation)
            if reduced and abs(reduced[min(reduced)])!=1:
                raise ValueError('this basis order needs integral lattice reduction')
            space.insert(relation)
        for r,layer in enumerate(self.layers):
            for i,w in enumerate(layer):
                if not survives(w):
                    impose(relations[r],{i:1})
                    impose(relations[r-1],{self.indices[r-1][f]:n for f,n in self.boundary(w).items()})
        self.generators = [[vector(space.reduce({i:1})) for i in range(len(layer))]
                           for layer,space in zip(self.layers,relations)]
        self.labels = [[tuple((d,x) if d else () for d,x in w) for w in layer]
                       for layer in self.layers]
        self.components = []
        self.categories = []
        self.atoms = {}
        for r,layer in enumerate(self.layers[:rank+1]):
            # Only generators sharing a normal-form coordinate can interact.
            groups = [{i for i,_ in g} for g in self.generators[r] if g]
            parts = []
            for group in groups:
                touching = [p for p in parts if p & group]
                for p in touching:
                    parts.remove(p)
                    group.update(p)
                parts.append(group)
            self.components.append({i:j for j,g in enumerate(parts) for i in g})
            categories = defaultdict(set)
            for i,g in enumerate(self.generators[r]):
                if g:
                    categories[self.components[r][g[0][0]],self.labels[r][i]].add(g)
                rows = self.atom_table(r,i)
                self.atoms[rows] = (r,i)
            self.categories.append(categories)

    def boundary(self,w):
        return dict(facets(self.trees,w))

    def row(self,r,indices):
        value = ()
        for i in indices:
            value = add(value,self.generators[r][i])
        return value

    def atom_table(self,r,i):
        rows = atom(self.layers[r][i],self.boundary)
        return tuple(tuple(self.row(j,[self.indices[j][w] for w in side]) for side in pair)
                     for j,pair in enumerate(rows))

    @cache
    def differential(self,r,v):
        result = Counter()
        for i,n in v:
            for f,k in self.boundary(self.layers[r][i]).items():
                for j,c in self.generators[r-1][self.indices[r-1][f]]:
                    result[j] += n*k*c
        return vector(result)

    @cache
    def component_sums(self,r,component,counts):
        choices = [combinations_with_replacement(self.categories[r][component,label],n)
                   for label,n in counts]
        sums = defaultdict(set)
        for groups in product(*choices):
            generators = sum(groups,())
            row = ()
            for g in generators:
                row = add(row,g)
            sums[row].update(generators)
        return sums

    @cache
    def divisors(self,r,v):
        """All single basis summands of a positive row. None denotes infeasibility."""
        by_component = defaultdict(dict)
        for i,n in v:
            by_component[self.components[r][i]][i] = n
        possible = set()
        for component,entries in by_component.items():
            counts = Counter()
            for i,n in entries.items():
                counts[self.labels[r][i]] += n
            if min(counts.values())<0:
                return None
            key = tuple(sorted((label,n) for label,n in counts.items() if n))
            options = self.component_sums(r,component,key).get(vector(entries))
            if options is None:
                return None
            possible.update(options)
        return frozenset(possible)


def compose(c,d,cut):
    """Steiner tableau composition, checking the entire lower seam."""
    n = max(len(c),len(d),cut+2)
    c += (((),()),)*(n-len(c))
    d += (((),()),)*(n-len(d))
    if c[:cut]!=d[:cut] or c[cut][1]!=d[cut][0]:
        raise ValueError('incompatible quotient seam')
    upper = tuple(tuple(add(a,b) for a,b in zip(x,y)) for x,y in zip(c[cut+1:],d[cut+1:]))
    return c[:cut]+((c[cut][0],d[cut][1]),)+upper


class Pasting:
    def __init__(self,chart):
        self.chart = chart
        self.proofs = {}

    @cache
    def generated(self,c):
        if c in self.chart.atoms:
            self.proofs[c] = ('atom',*self.chart.atoms[c])
            return True
        if c[-1]==((),()) and len(c)>1:
            if self.generated(c[:-1]):
                self.proofs[c] = ('id',c[:-1])
                return True
            return False
        for cut,a,b in self.splits(c):
            if self.join(c,cut,a,b):
                return True
        return False

    def splits(self,c):
        q = len(c)-1
        if q==0:
            return
        top = c[-1][0]
        assert c[-1][1]==top
        possible = self.chart.divisors(q,top)
        if not possible:
            return
        if mass(top)>1:
            for g in sorted(possible):
                seam = add(c[q-1][0],self.chart.differential(q,g))
                if self.chart.divisors(q-1,seam) is None:
                    continue
                rest = minus(top,g)
                a = c[:q-1]+((c[q-1][0],seam),(g,g))
                b = c[:q-1]+((seam,c[q-1][1]),(rest,rest))
                yield q-1,a,b
            return
        for r in range(q-1,0,-1):
            src,tgt = c[r]
            common = self.chart.divisors(r,src) & self.chart.divisors(r,tgt)
            lo,hi = c[r-1]
            for g in sorted(common):
                rest = (minus(src,g),minus(tgt,g))
                d = self.chart.differential(r,g)
                for first in (True,False):
                    seam = add(lo,d) if first else minus(hi,d)
                    if self.chart.divisors(r-1,seam) is None:
                        continue
                    left,right = (lo,seam),(seam,hi)
                    stationary,moving = (left,right) if first else (right,left)
                    piece = c[:r-1]+(stationary,(g,g))
                    remaining = c[:r-1]+(moving,rest)+c[r+1:]
                    a,b = (piece,remaining) if first else (remaining,piece)
                    yield r-1,a,b
        return

    def join(self,cell,cut,left,right):
        if self.generated(left) and self.generated(right):
            self.proofs[cell] = ('compose',cut,left,right)
            return True
        return False

    def certificate(self,goals):
        records = []
        @cache
        def visit(c):
            op,*args = self.proofs[c]
            if op=='compose':
                k,a,b = args
                args = [k,visit(a),visit(b)]
            elif op=='id':
                args = [visit(args[0])]
            records.append([op,*args])
            return len(records)-1
        roots = [visit(c) for c in goals]
        return {'records':records,'roots':roots}


def replay(chart,proof):
    values = []
    for op,*args in proof['records']:
        if op=='atom':
            v = chart.atom_table(*args)
        elif op=='id':
            v = values[args[0]]+(((),()),)
        elif op=='compose':
            cut,a,b = args
            v = compose(values[a],values[b],cut)
        else:
            raise ValueError(op)
        values.append(v)
    return [values[i] for i in proof['roots']]


def only_these_rows(chart,faces,choices):
    """Exclude all other local 5-chains at the concrete old faces in the quotient."""
    lines = ['(set-logic QF_LIA)']
    contributions = defaultdict(list)
    for j,g in enumerate(chart.generators[5]):
        assert g==((j,1),)
        v = f'x{j}'
        lines.extend((f'(declare-const {v} Int)',f'(assert (>= {v} 0))'))
        for i,n in chart.differential(5,g):
            contributions[i].extend([v if n>0 else f'(- {v})']*abs(n))
    delta = dict(minus(faces[1],faces[0]))
    for i in contributions.keys() | delta.keys():
        lines.append(f'(assert (= {total(contributions[i])} {delta.get(i,0)}))')
    for indices in choices:
        cond = ' '.join(f'(= x{j} {int(j in indices)})' for j in range(len(chart.layers[5])))
        lines.append(f'(assert (not (and {cond})))')
    return check('\n'.join(lines+['(check-sat)']))=='unsat'


def old_boundary_lifts(chart,rows):
    """Ask for a simultaneous old lift of both sides in every supplied row."""
    lines = ['(set-logic QF_LIA)']
    delta = {}
    for r,pair in enumerate(rows):
        faces = []
        for h,target in enumerate(pair):
            terms = defaultdict(list)
            raw_boundary = defaultdict(list)
            names = []
            for i,g in enumerate(chart.generators[r]):
                v = f'r{r}_{h}_{i}'
                names.append(v)
                lines.extend((f'(declare-const {v} Int)',f'(assert (>= {v} 0))'))
                for j,n in g:
                    terms[j].extend([v if n>0 else f'(- {v})']*abs(n))
                for f,n in chart.boundary(chart.layers[r][i]).items():
                    raw_boundary[chart.indices[r-1][f]].append(v if n>0 else f'(- {v})')
            wanted = dict(target)
            for j in terms.keys() | wanted.keys():
                lines.append(f'(assert (= {total(terms[j])} {wanted.get(j,0)}))')
            if r:
                for j,previous in delta.items():
                    lines.append(f'(assert (= {total(raw_boundary[j])} {previous}))')
            else:
                lines.append(f'(assert (= {total(names)} 1))')
            faces.append(names)
        delta = {j:f'(- {b} {a})' for j,(a,b) in enumerate(zip(*faces))}
    return check('\n'.join(lines+['(check-sat)']))


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('--emit',type=Path)
    p.add_argument('--replay',type=Path)
    args = p.parse_args()
    chart = Chart([[[[]]],[[[[]],[[]]]],[[[]]]],5)
    old = tuple(tuple(chart.row(r,side) for side in pair) for r,pair in enumerate(certificate_rows()))
    choices = [[5,8,14,19,j,23,30] for j in (20,21,22)]
    goals = [old+((chart.row(5,s),)*2,) for s in choices]
    assert only_these_rows(chart,old[-1],choices)
    serial = compose(compose(chart.atom_table(5,8),chart.atom_table(5,21),1),chart.atom_table(5,19),1)
    assert old_boundary_lifts(chart,serial[:3])=='sat'
    assert old_boundary_lifts(chart,serial[:4])=='unsat'
    print('The serial surface paste lifts through local rank two and has no common old lift through rank three.')
    if args.replay:
        proof = json.loads(args.replay.read_text())
    else:
        search = Pasting(chart)
        for goal in goals:
            assert search.generated(goal)
        proof = search.certificate(goals)
    assert replay(chart,proof)==goals
    if args.emit:
        args.emit.write_text(json.dumps(proof,separators=(',',':'))+'\n')
    print(f"All three quotient fillers replayed using {len(proof['records'])} distinct atom, identity and composition records.")
