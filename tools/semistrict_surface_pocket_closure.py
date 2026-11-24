"""Enclose an ordinary point-rule movie in a temporary wired lens.

For serial one-object point-gate input, return the wired history, the scalar
history retaining one boundary gate, and their probe sphere counts. The
optional placement refers to a gap in the input point movie.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from semistrict_surface_event_holes import plat
from semistrict_surface_movie_spine import expanded
from semistrict_surface_serial_gate_tracks import read_track
from semistrict_surface_spherical_relations import analyze


def enclose(data,mode):
    if mode not in ('wired','anchored','unanchored'):
        raise ValueError('unknown pocket reading')
    if data['path'] or any(s or t or x!=data['vertex'] for x,s,t in data['gates'].values()):
        raise ValueError('the pocket interior must have point gates at one object')
    read_track(dict(data,charts=[dict(c,loop=()) for c in data['charts']]),require_shared_gate=False)
    wired = mode=='wired'
    anchor = mode!='unanchored'
    gates = dict(data['gates'])
    def new(label,s,t):
        while label in gates:
            label += '_'
        gates[label] = [data['vertex'],s,t]
        return label
    site = new('pocket_site','aa' if wired else '','aa' if wired else '')
    first = [(int(wired),new('pocket_split','a' if wired else '','aa' if wired else ''))] if anchor else []
    last = [(1,new('pocket_merge','aa','a'))] if wired else []
    def inside(rows):
        return first+[(2 if wired else 0,g) for _,g in rows]+last
    charts = data['charts']
    open_site = [(0,site)]
    begin = dict(diagram=open_site,slot=0,input=[],output=inside(expanded(charts[0],'input')))
    end = dict(diagram=open_site,slot=0,input=inside(expanded(charts[-1],'output')),output=[])
    def shift(word):
        return [g+(len(first) if g>0 else -len(first)) for g in word]
    middle = [dict(c,diagram=inside(c['diagram']),slot=c['slot']+len(first)) for c in charts]
    for c in middle:
        if 'loop' in c:
            c['loop'] = shift(c['loop'])
    seams = [shift(word) for word in data['seams']]
    probes = data.get('probes',[])
    if 'placement' not in data and len(probes)>1:
        raise ValueError('select the input position with placement')
    gap,row,pos = data.get('placement',probes[0] if probes else [0,0,0])
    cuts = [expanded(charts[0],'input')]+[expanded(c,'output') for c in charts]
    if not 0<=gap<len(cuts) or not 0<=row<=len(cuts[gap]):
        raise ValueError('placement outside the selected cut')
    if pos:
        raise ValueError('a scalar cut has only wire gap zero')
    return dict(vertex=data['vertex'],edges={'a':[data['vertex']]*2} if wired else {},path='aa' if wired else '',
                gates=gates,charts=[begin,*middle,end],seams=[[],*seams,[]],
                placement=[gap+1,row+len(first),2 if wired else 0])


def compare(data):
    results = {key:analyze(enclose(data,key)) for key in ('wired','anchored','unanchored')}
    actual,flat = results['wired'],results['anchored']
    b0,b1,b2 = actual['betti']
    assert flat['betti']==[b0,b1,b2+1]
    assert flat['sphere_orbits']==actual['sphere_orbits']+1
    return {key:{field:r[field] for field in ('generators','faces','betti','sphere_orbits')} for key,r in results.items()}


def caps(word):
    names = list('pbc')
    for g in word:
        i = abs(g)-1
        names[i:i+2] = names[i:i+2][::-1]
    # The terminal cap takes the last two strands in their actual order.
    point = lambda names:[(0,g) for g in names]
    charts = [dict(diagram=point('pH'),slot=1,input=[],output=point('bc')),
              dict(diagram=point([names[0],'H']),slot=1,input=point(names[1:]),output=[])]
    return dict(vertex='x',path='',edges={},gates={g:['x','',''] for g in 'pbcH'},
                charts=charts,seams=[word])


def audit():
    tested = 0
    for length in range(4):
        for word in product((1,-1,2,-2),repeat=length):
            compare(caps(word))
            tested += 1
    for length in range(3):
        for word in product((1,-1,2,-2,3,-3),repeat=length):
            compare(plat(word)[0])
            tested += 1
    untwisted = compare(caps([]))
    assert untwisted['wired']['betti']==[1,2,1] and untwisted['anchored']['betti']==[1,2,2]
    assert untwisted['unanchored']['betti']==[1,1,2]
    for g in (-1,1):
        hopf = compare(caps([g,g]))
        assert hopf['wired']['sphere_orbits']==0 and hopf['anchored']['sphere_orbits']==1
    # No internal cut particles: a blank-to-blank inner site is still a
    # point obstacle. The boundary arc itself accounts for the extra hole.
    point = dict(diagram=[(0,'H')],slot=0,input=[],output=[])
    scalar = dict(vertex='x',path='',edges={},gates={'H':['x','','']},charts=[point],seams=[])
    answer = compare(scalar)
    assert answer['wired']['betti']==[1,0,1] and answer['anchored']['betti']==[1,0,2]
    print(f'{tested} signed tangles and a blank-port site checked in all three readings')
    for name,value in untwisted.items():
        print(name,value)


def typed(directory):
    from catt import STAR,arr,check_ctx,comp2,infer,subst_tm,subst_ty,v
    from emit_agda import Emitter
    from relative_coherence_exchange_faces import head
    from relative_coherence_hidden_seam import identity

    point = (STAR,)
    u = identity(point,v(0))
    scalar = arr(infer(point,u),u,u)
    source = (STAR,arr(STAR,v(0),v(0)),scalar,scalar,scalar)
    a,p,b,c = map(v,(1,2,3,4))
    # The left and right copies of a position p inside the two branches.
    middle = comp2(source,0,comp2(source,0,a,p),a)
    _,_,lo,hi = infer(source,middle)
    source += (arr(infer(source,a),a,lo),arr(infer(source,a),hi,a))
    lens = comp2(source,1,comp2(source,1,v(5),middle),v(6))
    packet = comp2(source,0,a,lens)
    blank = identity(source,infer(source,packet)[2])
    empty = identity(source,u)
    pair = comp2(source,1,b,c)
    source += tuple(arr(infer(source,s),s,t) for s,t in
                    [(blank,packet),(packet,blank),(empty,pair),(pair,empty)])
    check_ctx(source)
    # Flat scalar colours: p,b,c, then the retained boundary gate.
    target = point+(scalar,)*4
    images = [v(0),u,v(1),v(2),v(3)]
    dest = subst_tm(lo,images)
    images.append(comp2(target,1,v(4),head(point,u,dest)))
    images.append(head(point,subst_tm(hi,images),u))
    for i in range(7,len(source)):
        target += (subst_ty(source[i],images),)
        images.append(v(len(target)-1))
    check_ctx(target)
    for i,ty in enumerate(source):
        assert infer(target,images[i])==subst_ty(ty,images[:i])
    emitter = Emitter()
    for name,term in [('wiredOpening',v(7)),('wiredClosing',v(8)),('innerBirth',v(9)),
                      ('innerDeath',v(10)),('placedCaps',comp2(source,2,v(7),v(8)))]:
        image = subst_tm(term,images)
        ty = subst_ty(infer(source,term),images)
        assert infer(target,image)==ty
        if directory:
            emitter.check_type(name,target,image,ty)
    if directory:
        emitter.check_type('splitColourAtWiredEnds',target,images[5],subst_ty(source[5],images))
        emitter.check_type('mergeFitAtWiredEnds',target,images[6],subst_ty(source[6],images))
        (directory/'PocketClosure.agda').write_text(emitter.module('PocketClosure',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--emit',choices=['wired','anchored','unanchored'])
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        result = enclose(data,args.emit) if args.emit else compare(data)
        print(json.dumps(result,indent=2))
    else:
        audit()
        typed(args.agda_dir)
