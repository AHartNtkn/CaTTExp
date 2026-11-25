"""Saturate planar factors in finite strict 2-categories and strengthen typed old queries."""
from argparse import ArgumentParser
from collections import defaultdict
from functools import cache
from itertools import permutations, product
from pathlib import Path
from typing import NamedTuple

from catt import (STAR, arr, check_ctx, comp2, fv_ty, infer, restrict, subst_tm,
                  subst_ty, tdim, v)
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity


class Cell(NamedTuple):
    src: str
    tgt: str
    value: tuple
    marked: bool = False


def multiply(g, h):
    return tuple(h[i] for i in g)


E = (0, 1, 2)
GROUP = tuple(permutations(E))


class ArrowCategory:
    def __init__(self, unit, mul, absorbed):
        self.unit, self.mul, self.absorbed = unit, mul, absorbed

    def canonical(self, c):
        if (c.src,c.tgt,c.value) == ('i','o',self.absorbed):
            return c._replace(marked=False)
        return c

    def vertical(self, a, b):
        if a.tgt == b.src:
            return self.canonical(Cell(a.src,b.tgt,self.mul(a.value,b.value),a.marked or b.marked))

    def horizontal(self, a, b):
        if a.src == 'S' and b.src != 'T':
            return self.canonical(b._replace(marked=a.marked or b.marked))
        if a.src != 'S' and b.src == 'T':
            return a


class Probe(ArrowCategory):
    def __init__(self, absorbed):
        super().__init__(E, multiply, absorbed)
        self.cells = {Cell('S','S',E), Cell('S','S',E,True), Cell('T','T',E)}
        for i, s in enumerate('imo'):
            for t in 'imo'[i:]:
                for g in GROUP if s != t or s == 'm' else [E]:
                    for flag in (False,True):
                        self.cells.add(self.canonical(Cell(s,t,g,flag)))
        self.tables = []
        for op in (self.vertical, self.horizontal):
            table = {}
            for a,b in product(self.cells, repeat=2):
                c = op(a,b)
                if c is not None:
                    assert c in self.cells
                    table[a,b] = c
            self.tables.append(table)

    def laws(self):
        ver, hor = self.tables
        for op in self.tables:
            for (a,b), ab in op.items():
                for c in self.cells:
                    assert op.get((ab,c)) == op.get((a,op.get((b,c))))
        for (a,b), ab in hor.items():
            for (c,d), cd in hor.items():
                if (a,c) in ver and (b,d) in ver:
                    assert ver[ab,cd] == hor[ver[a,c],ver[b,d]]
        for c in self.cells:
            assert ver[Cell(c.src,c.src,E),c] == ver[c,Cell(c.tgt,c.tgt,E)] == c
            left = 'T' if c.src == 'T' else 'S'
            right = 'S' if c.src == 'S' else 'T'
            assert hor[Cell(left,left,E),c] == hor[c,Cell(right,right,E)] == c

    def factors(self, target):
        """Close under both factors of every well-typed composition."""
        children = defaultdict(set)
        for table in self.tables:
            for (a,b), c in table.items():
                children[c].update((a,b))
        found = {target}
        todo = [target]
        while todo:
            new = children[todo.pop()] - found
            found.update(new)
            todo.extend(new)
        return found


def example(bicyclic_equation=False):
    ctx = (STAR,STAR) + (arr(STAR,v(0),v(1)),)*3 + (arr(STAR,v(0),v(0)),)
    i,m,o,h = map(v, range(2,6))
    unit = identity(ctx,v(0))

    def arrow(s,t):
        assert infer(ctx,s) == infer(ctx,t)
        return arr(infer(ctx,s),s,t)

    ctx += (arrow(unit,h), arrow(h,unit), arrow(i,m), arrow(m,o), arrow(m,m), arrow(m,m))
    birth, death, left, right, g, k = map(v, range(6,12))
    bubble = comp2(ctx,1,birth,death)
    base = comp2(ctx,1,left,right)
    guarded = comp2(ctx,0,identity(ctx,unit),base), comp2(ctx,0,bubble,base)
    ctx += (arrow(*guarded),)
    if bicyclic_equation:
        ctx += (arrow(comp2(ctx,1,g,k),identity(ctx,m)),)
        g,k = k,g
    old = comp2(ctx,1,comp2(ctx,1,left,comp2(ctx,1,g,k)),right)
    j = len(ctx)
    ctx += (arrow(old,old),)
    ctx += (arrow(v(j),v(j)),)*3
    ctx += (arrow(v(j+1),v(j+2)),arrow(v(j+2),v(j+3)))
    term = comp2(ctx,4,v(j+4),v(j+5))
    assert infer(ctx,term) == arrow(v(j+1),v(j+3))
    check_ctx(ctx)
    return ctx, guarded, term


def fixture_grades(probe, ctx, first, second):
    e = probe.unit
    values = ['s','t','i','m','o','S', Cell('S','S',e,True), Cell('S','S',e,True),
              Cell('i','m',e), Cell('m','o',e), Cell('m','m',first), Cell('m','m',second)]
    # Read the dimensional shadow of each generic composite from its tree.
    # Parallel versions of a 2-cell in a deeper string have the same value.
    @cache
    def read(t):
        if t[0] == 'v':
            return values[t[1]]
        _, arity, ty, labels = t
        rank = tdim(ty)+1
        vertices = [j for j,a in enumerate(arity) if a == STAR]
        origin = read(labels[vertices[0]])
        unit = 'S' if origin == 's' else 'T'
        if rank == 0:
            return origin
        shadow = Cell(unit,unit,e)
        for s,u in zip(vertices,vertices[1:]):
            arrows = [j for j,a in enumerate(arity) if a == arr(STAR,v(s),v(u))]
            start = read(labels[arrows[0]])
            column = Cell(start,start,e)
            for j,k in zip(arrows,arrows[1:]):
                between = [read(labels[n]) for n,a in enumerate(arity)
                           if a == arr(arity[j],v(j),v(k))]
                assert between and all(c == between[0] for c in between)
                column = probe.vertical(column,between[0])
            shadow = probe.horizontal(shadow,column)
            assert shadow is not None
        return shadow.src if rank == 1 else shadow
    for ty in ctx[len(values):]:
        a,b = read(ty[2]), read(ty[3])
        assert a == b
        values.append(a)
    return values, read


def strengthen(ctx, term, keep):
    assert all(fv_ty(ctx[j]) <= set(keep) for j in keep)
    subctx, inclusion = restrict(ctx,keep)
    back = {a[1]:v(j) for j,a in enumerate(inclusion)}
    lifted = subst_tm(term,back)
    expected = subst_ty(infer(ctx,term),back)
    check_ctx(subctx)
    assert infer(subctx,lifted) == expected
    assert subst_tm(lifted,inclusion) == term and subst_ty(expected,inclusion) == infer(ctx,term)
    return subctx, lifted, expected


def check_fix(output):
    ctx, guarded, term = example()
    e = Emitter()
    probe = Probe(E)
    reads = 0
    for g,k in product(GROUP,repeat=2):
        values, read = fixture_grades(probe, ctx, g,k)
        assert read(guarded[0]) == read(guarded[1]) == Cell('i','o',E)
        p = read(term)
        assert p == Cell('i','o',multiply(g,k))
        div = probe.factors(p)
        keep = [j for j,c in enumerate(values) if j < 6 or c in div]
        assert (6 in keep) == (7 in keep) == (12 in keep) == (p.value == E)
        subctx, lifted, expected = strengthen(ctx,term,keep)
        if p.value != E:
            reads += 1
            if output and reads == 1:
                e.check_type('localizedComposite',subctx,lifted,expected)
                e.check_type('originalComposite',ctx,term,infer(ctx,term))
                e.check_type('birthDeathRelation',ctx,v(12),ctx[12])
    print('36 group-labelled degree-five queries;', reads, 'exclude both empty poles and refold literally')
    ctx, guarded, term = example(bicyclic_equation=True)
    one = (0,0)
    values, read = fixture_grades(ArrowCategory(one,bicyclic,one),ctx,(0,1),(1,0))
    assert read(term) == Cell('i','o',(1,1)) and read(guarded[1]) == Cell('i','o',one)
    keep = [j for j,c in enumerate(values) if j < 6 or not (c.marked or c == Cell('i','o',one))]
    assert set(range(len(ctx))) - set(keep) == {6,7,12}
    subctx, lifted, expected = strengthen(ctx,term,keep)
    if output:
        e.check_type('bicyclicRelation',ctx,v(13),ctx[13])
        e.check_type('bicyclicLocalizedComposite',subctx,lifted,expected)
        (output/'PlanarDivisorChecks.agda').write_text(e.module('PlanarDivisorChecks',__doc__))


def bicyclic(a,b):
    i,j = a
    k,l = b
    common = min(j,k)
    return i+k-common, j+l-common


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    for absorbed in GROUP:
        probe = Probe(absorbed)
        probe.laws()
        for g in GROUP:
            factors = probe.factors(Cell('i','o',g))
            assert (Cell('S','S',E,True) in factors) == (g == absorbed)
    check_fix(args.agda_dir)
    p,q = (0,1),(1,0)
    assert bicyclic(p,q) == (0,0) != bicyclic(q,p)
    normal = [(i,j) for i,j in product(range(5),repeat=2)]
    for a,b,c in product(normal,repeat=3):
        assert bicyclic(bicyclic(a,b),c) == bicyclic(a,bicyclic(b,c))
    print('36 saturated factor tests; bicyclic pq and qp:', bicyclic(p,q), bicyclic(q,p))


if __name__ == '__main__':
    main()
