"""Separate integral collision-sphere coefficients during a planar lens's lifetime.

JSON supplies children (positive gate counts; 1 for a point, at least 2 for a
lens with that many gates), and terms [coefficient, fixed-probe name, access
word]. A signed one-based access word winds around the named children. The
moving probe is common to all terms. The outer lens is born and then consumed.
"""
from argparse import ArgumentParser
from collections import Counter
from itertools import product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, src, tgt, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_chain_probe import evaluate
from semistrict_surface_gap_linking import cover, lift
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_probe_retraction import probe_word, project
from semistrict_surface_serial_gate_tracks import push


def positions(sizes):
    gates = {g:['x','',''] for g in ('probe','site','spectator')}
    rows = []
    def lens(name):
        gates[name+'b'] = ['x','','aa']
        gates[name+'d'] = ['x','aa','']
        return name+'b',name+'d'
    b,d = lens('outer')
    rows.extend([(0,b),(1,'probe')])
    for i,size in enumerate(sizes):
        if type(size) is not int or size<1:
            raise ValueError('each child must contain at least one gate')
        name = f'h{i}'
        if size==1:
            gates[name] = ['x','','']
            rows.append((1,name))
        else:
            left,right = lens(name)
            rows.append((1,left))
            for k in range(size-2):
                point = f'{name}i{k}'
                gates[point] = ['x','','']
                rows.append((2,point))
            rows.append((1,right))
    rows.extend([(0,d),(0,'spectator')])
    base = dict(edges={'a':['x','x']},gates=gates,vertex='x',path='',diagram=rows,probe='probe')
    packet = [(0,g) for _,g in rows if g not in ('probe','spectator')]
    def rule(a,b):
        return dict(diagram=[(0,'site'),(0,'spectator')],slot=0,input=a,output=b)
    flat = dict(base,gates={g:['x','',''] for g in gates},charts=[rule([],packet),rule(packet,[])],
                seams=[[]])
    complete = evaluate(flat)
    assert complete['attaching_word']==()
    prefix = evaluate(dict(flat,charts=flat['charts'][:1],seams=[]))
    return base,prefix['final_meridians'],complete['generators']


def solve(data):
    sizes = data['children']
    base,frame,rank = positions(sizes)
    cached = {}
    source,flattened = Counter(),Counter()
    for coeff,fixed,letters in data['terms']:
        if type(coeff) is not int or not isinstance(fixed,str) or not fixed:
            raise ValueError('expected an integral coefficient and a fixed-probe name')
        if any(type(x) is not int or not 1<=abs(x)<=len(sizes) for x in letters):
            raise ValueError('access word contains an unknown meridian')
        w = reduced(letters)
        if w not in cached:
            # Execute the interior access on actual gate strands. Read its
            # flattened image in the swept free basis, including the rule
            # which attached the enclosing lens at the initial empty port.
            local = cable(push(w),[1,*sizes])
            positioned = tuple((abs(x)+1)*(1 if x>0 else -1) for x in local)
            assert project(dict(base,loop=positioned))['word']==w
            all_gates = probe_word(len(base['diagram']),(1,)+positioned+(-1,))
            cached[w] = reduced(tuple(a for g in all_gates for a in
                                (frame[g-1] if g>0 else inv(frame[-g-1]))))
        source[fixed,w] += coeff
        flattened[fixed,cached[w]] += coeff
    assert len(set(cached.values()))==len(cached)
    support = {key:c for key,c in flattened.items() if c}
    sheets,rows = cover({w for _,w in support},rank)
    origin = sheets.index(())
    reading = Counter()
    for (name,w),c in support.items():
        reading[name,lift(w,origin,rows)] += c
    assert sorted(reading.values())==sorted(c for c in source.values() if c)
    return dict(flat_generators=rank,sheets=len(sheets),collision_coefficients=[
                [c,name,sheet] for (name,sheet),c in sorted(reading.items())])


def audit():
    # Separated named fixed probes, negative coefficients, nonzero differences
    # with zero augmentation, and different spellings of the same access path.
    for sizes in ([1,2],[3,1]):
        terms = []
        for length in range(4):
            for w in product((1,-1,2,-2),repeat=length):
                if reduced(w)==w:
                    for name in ('red','blue'):
                        terms.append([1 if name=='red' else -2,name,w])
                        terms.append([3,name,(1,-1)+w])
                        terms.append([-3,name,w+(2,-2)])
        r = solve(dict(children=sizes,terms=terms))
        assert len(r['collision_coefficients'])==106
        print(f'{sizes}: {len(terms)} summands, 106 signed coefficients separated in {r["sheets"]} sheets')
    commutator = (1,2,-1,-2)
    delta = solve(dict(children=[3,2],terms=[[1,'fixed',()],[-1,'fixed',commutator]]))
    assert len(delta['collision_coefficients'])==2
    assert not solve(dict(children=[3,2],terms=[[1,'fixed',commutator],
                   [-1,'fixed',commutator+(1,-1)]]))['collision_coefficients']
    print('zero total linking, distinct lifted collision coefficients:',delta)


def typed(directory):
    ctx = (STAR,STAR,arr(STAR,v(0),v(1)),arr(STAR,v(1),v(0)))
    a,b = v(2),v(3)
    inner,outer = identity(ctx,v(1)),identity(ctx,v(0))
    path = comp2(ctx,0,comp2(ctx,0,a,inner),b)
    def between(s,t):
        return arr(infer(ctx,s),s,t)
    ctx += (between(outer,path),between(path,outer),between(inner,inner))
    blank = identity(ctx,inner)
    ctx += (between(blank,blank),)*2
    inside = comp2(ctx,1,comp2(ctx,1,v(7),v(6)),v(8))
    enclosed = comp2(ctx,1,comp2(ctx,1,v(4),comp2(ctx,0,comp2(ctx,0,a,inside),b)),v(5))
    empty = identity(ctx,outer)
    assert src(ctx,enclosed)==tgt(ctx,enclosed)
    ctx += (between(empty,src(ctx,enclosed)),between(tgt(ctx,enclosed),empty))
    check_ctx(ctx)
    chain = comp2(ctx,2,comp2(ctx,2,v(9),enclosed),v(10))
    assert infer(ctx,chain)==between(empty,empty)
    if directory:
        out = Emitter()
        out.check_type('twoProbesInATemporaryFace',ctx,chain,between(empty,empty))
        (directory/'CollisionSheets.agda').write_text(out.module('CollisionSheets',__doc__.splitlines()[0]))


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('input',nargs='?',type=Path)
    p.add_argument('--agda-dir',type=Path)
    args = p.parse_args()
    if args.input:
        print(json.dumps(solve(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
        typed(args.agda_dir)
