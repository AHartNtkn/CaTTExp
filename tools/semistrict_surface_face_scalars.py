"""Compute face assignments and scalar windings in an anchored lower change chart."""

from argparse import ArgumentParser
from collections import defaultdict
from functools import lru_cache
from itertools import product
from math import gcd
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_component_braids import Partition
from semistrict_surface_planar_occurrences import component_transport

INITIAL = 'ha'
CORE = {'death': ('h',''), 'birth': ('','j'), 'split': ('a','bc'), 'merge': ('Bc','d')}
RULES = {**CORE, 'wire': ('b','B'), 's': ('',''), 't': ('',''),
         'direct': ('b','B'), 'open': ('b','z'), 'close': ('z','B')}
ROOT = (('death',0), ('split',0), ('wire',0), ('merge',0), ('birth',0))


def apply(word, g, i):
    src, tgt = RULES[g]
    assert 0 <= i <= len(word)-len(src) and word.startswith(src, i)
    return word[:i]+tgt+word[i+len(src):]


def signed_moves(h):
    for k, ((a,i),(b,j)) in enumerate(zip(h,h[1:])):
        u,v = map(len,RULES[a])
        p,q = map(len,RULES[b])
        if j+p <= i:
            yield k, 1, h[:k]+((b,j),(a,i+q-p))+h[k+2:]
        if i+v <= j:
            yield k, -1, h[:k]+((b,j-v+u),(a,i))+h[k+2:]


def central():
    words = {ROOT}
    todo = [ROOT]
    while todo:
        for _,_,nxt in signed_moves(todo.pop()):
            if nxt not in words:
                words.add(nxt)
                todo.append(nxt)
    return words


@lru_cache(None)
def faces(base):
    regions = Partition()
    tags = defaultdict(set)
    word = INITIAL
    widths = [len(word)]
    for j in range(len(word)+1):
        tags[0,j].add(('initial', j))
    for k, (g,i) in enumerate(base):
        a,b = map(len,RULES[g])
        for j in range(i+1):
            regions.unite((k,j),(k+1,j))
        for j in range(i+a,len(word)+1):
            regions.unite((k,j),(k+1,j+b-a))
        if g in CORE:
            for side, h, size in [('in',k,a), ('out',k+1,b)]:
                for j in range(size+1):
                    tags[h,i+j].add((g,side,j))
        word = apply(word,g,i)
        widths.append(len(word))
    assert word == 'jd'
    for j in range(len(word)+1):
        tags[len(base),j].add(('final', j))
    names = defaultdict(set)
    for spot, labels in tags.items():
        names[regions.at(spot)].update(labels)
    return tuple(tuple(frozenset(names[regions.at((k,j))]) for j in range(width+1))
                 for k,width in enumerate(widths))


def decorate(h, word, scalars, prefix=()):
    if not h and not scalars:
        yield prefix
    if h:
        g,i = h[0]
        yield from decorate(h[1:], apply(word,g,i), scalars, prefix+((g,i),))
    for s in scalars:
        for i in range(len(word)+1):
            yield from decorate(h, word, scalars-{s}, prefix+((s,i),))


def read(h):
    base = tuple((g,i) for g,i in h if g not in ('s','t'))
    tiers = faces(base)
    slots = {}
    k = 0
    for g,i in h:
        if g in ('s','t'):
            slots[g] = tiers[k][i]
        else:
            k += 1
    return slots['s'], slots['t']


def replace(h, steps):
    return tuple(row for g,i in h for row in
                 ([(name,i) for name in steps] if g == 'wire' else [(g,i)]))


def audit():
    base = central()
    words = {w for c in base for w in decorate(c, INITIAL, {'s','t'})}
    all_faces = {f for row in faces(ROOT) for f in row}
    assert all_faces and all(all_faces)
    enclosed = [f for f in all_faces if all(tag[0] not in ('initial','final') for tag in f)]
    assert len(enclosed) == 1
    found = {}
    for root, lifts, rigid in component_transport(words, RULES):
        assert rigid
        key = read(root)
        assert key not in found
        winding = {root:0}
        todo = [root]
        period = 0
        while todo:
            h = todo.pop()
            assert read(h) == read(replace(h, ('direct',))) == read(replace(h, ('open','close'))) == key
            for k, sign, nxt in signed_moves(h):
                assert nxt in lifts
                delta = sign if {h[k][0], h[k+1][0]} == {'s','t'} else 0
                value = winding[h] + delta
                if nxt in winding:
                    period = gcd(period, value-winding[nxt])
                else:
                    winding[nxt] = value
                    todo.append(nxt)
        assert len(lifts) == len(winding)
        assert period == (2 if key[0] == key[1] else 0)
        found[key] = period
    assert set(found) == set(product(all_faces, repeat=2))
    print('central spellings', len(base), 'decorated spellings', len(words), 'faces', len(all_faces),
          'ordered face pairs', len(found))
    print('pairs admitting a full turn', sum(v == 2 for v in found.values()),
          'pairs with zero winding', sum(v == 0 for v in found.values()))
    print('interior face corners', sorted(enclosed[0]))


def typed_chart(output):
    ctx = (STAR,) + (arr(STAR, v(0), v(0)),)*8
    h,a,b,z,upper,c,d,j = map(v, range(1,9))
    unit = identity(ctx,v(0))
    def arrow(s,t):
        return arr(infer(ctx,s),s,t)
    merge = arrow(comp2(ctx,0,upper,c),d)
    ctx += (arrow(h,unit), arrow(unit,j), arrow(a,comp2(ctx,0,b,c)), merge, merge,
            arrow(b,upper), arrow(b,z), arrow(z,upper))
    wire = arrow(v(14),comp2(ctx,1,v(15),v(16)))
    recolour = arrow(v(12),v(13))
    pole = identity(ctx,unit)
    scalar = arrow(pole,pole)
    ctx += (wire,recolour,scalar)
    check_ctx(ctx)
    if output:
        name = 'FixedFaceScalars'
        e = Emitter()
        for k,label,A in [(17,'wireChange',wire), (18,'mergeChange',recolour), (19,'floating',scalar)]:
            e.check_type(label,ctx,v(k),A)
        g = e.ctx(ctx)
        e.checks.append(f'typed : {g} ⊢ctx\ntyped = from-just (checkCtx {g})\n')
        (output / (name+'.agda')).write_text(e.module(name,__doc__))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    audit()
    typed_chart(args.agda_dir)
