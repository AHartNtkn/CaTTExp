"""Compute directed planar intervals and recheck query terms at their restricted faces."""
from argparse import ArgumentParser
from collections import defaultdict, deque
from itertools import product
from pathlib import Path

from catt import arr, comp2, fv_ty, infer, src, tdim, tgt, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_planar_divisors import (ArrowCategory, Cell, E, GROUP, Probe,
                                               bicyclic, example, fixture_grades, multiply,
                                               strengthen)


def preorder(probe, steps):
    # Close the given 3-arrows under stationary 2-contexts and transitivity.
    contexts = defaultdict(list)
    for table in probe.tables:
        for (a,b), c in table.items():
            contexts[a].append((table,b,False))
            contexts[b].append((table,a,True))
    queue = deque(steps)
    seen = set()
    before = defaultdict(set)
    after = defaultdict(set)
    for a in probe.cells:
        queue.append((a,a))
    while queue:
        a,b = queue.popleft()
        if (a,b) in seen:
            continue
        assert (a.src,a.tgt) == (b.src,b.tgt)
        seen.add((a,b))
        queue.extend((p,b) for p in before[a])
        queue.extend((a,q) for q in after[b])
        before[b].add(a)
        after[a].add(b)
        for table,c,left in contexts[a]:
            key_a, key_b = ((c,a),(c,b)) if left else ((a,c),(b,c))
            queue.append((table[key_a],table[key_b]))
    return after


def window(probe, reach, a, b):
    mids = [p for p in reach[a] if b in reach[p]]
    return set().union(*(probe.factors(p) for p in mids))


def terms(cycle=False):
    ctx = example()[0][:12]
    birth,death,l,d,g,k = map(v,range(6,12))
    unit = identity(ctx,identity(ctx,v(0)))
    bubble = comp2(ctx,1,birth,death)
    base = comp2(ctx,1,l,d)
    def arrow(a,b):
        assert infer(ctx,a) == infer(ctx,b)
        return arr(infer(ctx,a),a,b)
    ctx += (arrow(unit,bubble),)
    emit = comp2(ctx,0,v(12),base)
    # Choose the two ends of the actual whiskering, including its weak units.
    clean, dirty = src(ctx,emit), tgt(ctx,emit)
    ctx += (arrow(dirty,clean),)
    returning = comp2(ctx,2,emit,v(13))
    assert infer(ctx,returning) == arrow(clean,clean)
    if cycle:
        pq, one = comp2(ctx,1,g,k), identity(ctx,v(3))
        ctx += (arrow(pq,one),arrow(one,pq))
        g,k = k,g
    old = comp2(ctx,1,comp2(ctx,1,l,comp2(ctx,1,g,k)),d)
    j = len(ctx)
    ctx += (arrow(old,old),)
    ctx += (arrow(v(j),v(j)),)*3
    ctx += (arrow(v(j+1),v(j+2)),arrow(v(j+2),v(j+3)))
    composite = comp2(ctx,4,v(j+4),v(j+5))
    return ctx, composite, returning


def restrict_2(ctx, baseline, accepted):
    keep = set()
    for j,ty in enumerate(ctx):
        dim = tdim(ty)+1
        if dim < 2 or (dim == 2 and baseline[j] in accepted) or (dim > 2 and fv_ty(ty) <= keep):
            keep.add(j)
    return keep


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    probe = Probe(None)  # Retain both bits even at the absorbing word.
    clean = Cell('i','o',E)
    e = Cell('S','S',E,True)
    steps = [(Cell('S','S',E),e), (clean._replace(marked=True),clean)]
    reach = preorder(probe,steps)
    undirected = preorder(probe,steps + [(b,a) for a,b in steps])
    ctx, term, returning = terms()
    count = 0
    for g,k in product(GROUP,repeat=2):
        values, read = fixture_grades(probe,ctx[:12],g,k)
        for j,expected in zip((12,13),steps):
            ty = ctx[j]
            assert (read(ty[2]),read(ty[3])) == expected
        p = Cell('i','o',multiply(g,k))
        assert e in window(probe,undirected,p,p)
        allowed = window(probe,reach,p,p)
        assert (e in allowed) == (p == clean)
        keep = restrict_2(ctx,values,allowed)
        subctx, lifted, ty = strengthen(ctx,term,keep)
        if e not in allowed:
            count += 1
            if count == 1 and args.agda_dir:
                emitter.check_type('restricted',subctx,lifted,ty)
    assert count == 30
    ctx, term, _ = terms(cycle=True)
    one = (0,0)
    infinite = ArrowCategory(one,bicyclic,None)
    values, read = fixture_grades(infinite,ctx[:12],(0,1),(1,0))
    u = Cell('i','o',(1,1))
    for j in (12,13,14,15):
        a,b = (read(t) for t in ctx[j][2:])
        assert (a.src,a.tgt,a.value) == (b.src,b.tgt,b.value)
        assert a.marked <= b.marked or (a.src,a.tgt,a.value) == ('i','o',one)
    assert read(ctx[16][2]) == u
    keep = restrict_2(ctx,values,{p for p in values[6:] if not p.marked})
    subctx, lifted, ty = strengthen(ctx,term,keep)
    print('36 undirected windows contain both gates; 30 directed windows exclude both')
    print('bicyclic directed restriction:',len(ctx),'declarations to',len(subctx))
    if args.agda_dir:
        orig = terms()[0]
        emitter.check_type('bubbleReturn',orig,returning,infer(orig,returning))
        emitter.check_type('infiniteWindow',subctx,lifted,ty)
        (args.agda_dir / 'DirectedPlanarDivisors.agda').write_text(
            emitter.module('DirectedPlanarDivisors',__doc__))


if __name__ == '__main__':
    main()
