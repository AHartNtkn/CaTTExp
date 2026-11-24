"""Decide a structural degree-five loop on a scalar chain inside a wired lens.

Input is a serial_gate_tracks point movie with a based loop at each site.
It describes the interior between the outer opening and closing. Output
includes the two-cap scalar detector in the spectator-only case.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from semistrict_surface_birth_death_packets import expand,expand_path,follow
from semistrict_surface_component_braids import restrict
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import inv,reduced
from semistrict_surface_movie_spine import expanded
from semistrict_surface_serial_gate_tracks import push,read_track
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_spherical_relations import analyze as spine


def trace(data):
    charts = data['charts']
    initial = expanded(charts[0],'input')
    marks = list(range(len(initial)))
    consumed = False
    transport = []
    for i,ch in enumerate(charts):
        j = ch['slot']
        end = j+len(ch['input'])
        consumed |= any(g is not None for g in marks[j:end])
        marks[j:end] = [None]*len(ch['output'])
        if i<len(data['seams']):
            seam = data['seams'][i]
            keep = {k for k,g in enumerate(marks) if g is not None}
            transport.extend(restrict(len(marks),seam,keep))
            for g in seam:
                k = abs(g)-1
                marks[k:k+2] = marks[k:k+2][::-1]
    return consumed,None in marks,marks,transport


def collar(data,marks,transport):
    # In the selected scalar specialization keep one split colour and all
    # initial gates. Use occurrence indices as names, even for equal colours.
    initial = ['s'+str(i) for i in range(len(marks))]
    first = ['shell',*initial]
    last = ['shell',*(initial[i] for i in marks)]
    row = lambda names:[(0,g) for g in names]
    joint = row(['cap'])
    charts = [dict(diagram=joint,slot=0,input=[],output=row(first)),
              dict(diagram=joint,slot=0,input=row(last),output=[])]
    x = data['vertex']
    seam = [g+(1 if g>0 else -1) for g in transport]
    return dict(vertex=x,path='',edges={},gates={g:[x,'',''] for g in ['cap',*first]},
                charts=charts,seams=[seam],placement=[1,0,0])


def analyze(data):
    if data['path'] or any(s or t or x!=data['vertex'] for x,s,t in data['gates'].values()):
        raise ValueError('expected a one-object point-gate chain')
    track = read_track(data)
    consumed,survives,marks,transport = trace(data)
    result = dict(inner_sites=track['sites'],raw_filler=not track['nonzero'],
                  consumed_initial=consumed,surviving_output=survives)
    if consumed or survives:
        assert result['raw_filler']
        return result
    first = data['charts'][0]
    index = first['slot']+1
    image = braid_image(len(marks)+1,first['loop'])[index-1]
    mid = len(image)//2
    stem = image[:mid]
    assert image==stem+(index,)+inv(stem)
    word = reduced(tuple(g if abs(g)<index else (1 if g>0 else -1)*(abs(g)-1)
                         for g in stem if abs(g)!=index))
    assert bool(word)==track['nonzero']
    result.update(spectator_conjugator=word,detector=collar(data,marks,transport))
    return result


def chain(m,arities,word,seam_motion=()):
    row = lambda names:[(0,g) for g in names]
    spectators = ['s'+str(i) for i in range(m)]
    blocks = [row([f'g{i}_{j}' for j in range(n)]) for i,n in enumerate(arities)]
    joint = row(['H',*spectators])
    charts,seams = [],[]
    for i,(a,b) in enumerate(zip(blocks,blocks[1:])):
        charts.append(dict(diagram=joint,slot=0,input=a,output=b,loop=word))
        if i<len(blocks)-2:
            seams.append(cable(seam_motion,[len(b)]+[1]*m))
            word = inv(seam_motion)+tuple(word)+tuple(seam_motion)
    names = ['H',*spectators,*(g for block in blocks for _,g in block)]
    return dict(vertex='x',path='',edges={},gates={g:['x','',''] for g in names},charts=charts,seams=seams)


def blank_end_test(data):
    from semistrict_surface_pocket_closure import enclose

    wrapped = enclose(data,'wired')
    if expanded(data['charts'][0],'input') or expanded(data['charts'][-1],'output'):
        raise ValueError('the unrestricted schedule test requires empty interior ends')
    charts = []
    for c in wrapped['charts'][1:-1]:
        rows = [(0,g) for q,g in c['diagram'][1:-1] if q==2]
        assert len(rows)==len(c['diagram'])-2
        charts.append(dict(diagram=rows,slot=c['slot']-1,input=c['input'],output=c['output']))
    seams = [[g-(1 if g>0 else -1) for g in seam] for seam in wrapped['seams'][1:-1]]
    scalar = dict(vertex=data['vertex'],path='',edges={},gates=data['gates'],charts=charts,seams=seams)
    read_track(dict(scalar,charts=[dict(c,loop=()) for c in charts]),require_shared_gate=False)
    return scalar


def tier_checks():
    # Follow a simultaneous diagram with three sites. Independently replace
    # each site by a port with zero, one, or two gates, and execute the signed
    # exchange both in the actual wired disk and in the projected plane.
    inner = ((0,'H0'),(0,'H1'),(0,'H2'))
    live = ((1,'split'),*((2,g) for _,g in inner),(1,'merge'))
    ports = dict(split=('a','aa'),merge=('aa','a'))
    checks = 0
    for sizes in product(range(3),repeat=3):
        packet = {g:tuple((0,g+str(k)) for k in range(n)) for (_,g),n in zip(inner,sizes)}
        ports.update({g:('','') for _,g in inner})
        ports.update({g:('','') for block in packet.values() for _,g in block})
        for length in range(3):
            for word in product((1,-1,2,-2),repeat=length):
                outside = tuple(g+(1 if g>0 else -1) for g in word)
                wired_path = expand_path(live,outside,packet)
                flat_path = expand_path(inner,word,packet)
                large = expand(live,packet)
                small = expand(inner,packet)
                dest = follow(large,wired_path,ports)
                assert all(q==2 for q,g in dest[1:-1])
                assert tuple((0,g) for _,g in dest[1:-1])==follow(small,flat_path,ports)
                kept = set(range(1,len(large)-1))
                assert restrict(len(large),wired_path,kept)==tuple(flat_path)
                checks += 1
    return checks


def audit():
    checked = 0
    for sizes in ([0,1,0],[0,3,2,0],[0,1,2,1,3,0]):
        for length in range(4):
            for word in product((1,-1,2,-2),repeat=length):
                result = analyze(chain(2,sizes,push(word)))
                assert result['spectator_conjugator']==reduced(tuple(reversed(word)))
                assert result['raw_filler']==(not reduced(word))
                checked += 1
    turns = (1,2,-1,-2)
    from semistrict_surface_pocket_closure import enclose
    example = chain(2,[0,2,1,0],push(turns),push([2]))
    moved = analyze(example)
    wired = enclose(example,'wired')
    read_track(dict(wired,charts=[dict(c,loop=c.get('loop',())) for c in wired['charts']]),
               require_shared_gate=False)
    assert moved['spectator_conjugator']==tuple(reversed(turns))
    assert spine(moved['detector'])['generators']==2
    for m in range(5):
        # A nontrivial seam on persistent spectators is retained even when
        # the tested site loop is constant.
        seam = (2,2) if m>=2 else ()
        data = chain(m,[0,2,0],(),seam)
        result = analyze(data)
        base = spine(result['detector'])
        assert base['betti']==[1,m,1] and base['generators']==m and not base['faces']
        assert result['detector']['seams']==[[2,2] if seam else []]
    for sizes,flags in [([1,2,0],(True,False)),([0,2,1],(False,True)),([1,2,1],(True,True))]:
        result = analyze(chain(2,sizes,()))
        assert (result['consumed_initial'],result['surviving_output'])==flags
        assert result['raw_filler']
    from semistrict_surface_event_holes import plat
    for w in ([],[1,-2,3],[-2,-2]):
        inner = plat(w)[0]
        flat = blank_end_test(inner)
        assert flat['charts']==inner['charts'] and flat['seams']==inner['seams']
    print(f'{tier_checks()} simultaneous spatial exchanges with port expansions agree after erasing the lens')
    print(f'{checked} chain loops agree with the independent spectator free-word calculation')
    print('transported commutator, signed spectator seams, five collar ranks and three endpoint cases checked')


def typed(directory):
    from catt import STAR,arr,check_ctx,comp2,infer,subst_tm,subst_ty,v
    from emit_agda import Emitter
    from relative_coherence_exchange_faces import head
    from relative_coherence_hidden_seam import identity

    point = (STAR,)
    u = identity(point,v(0))
    empty = identity(point,u)
    scalar = arr(infer(point,u),u,u)
    ctx = (STAR,arr(STAR,v(0),v(0)),scalar)
    a,b = v(1),v(2)
    ctx += (arr(scalar,empty,b),arr(scalar,b,empty))
    inside = comp2(ctx,2,v(3),v(4))
    def branches(cell):
        return comp2(ctx,0,comp2(ctx,0,a,cell),a)
    _,_,lo,hi = infer(ctx,branches(empty))
    ctx += (arr(infer(ctx,a),a,lo),arr(infer(ctx,a),hi,a))
    def place(cell):
        return comp2(ctx,0,a,comp2(ctx,1,comp2(ctx,1,v(5),branches(cell)),v(6)))
    port = place(empty)
    blank = identity(ctx,infer(ctx,port)[2])
    ctx += (arr(infer(ctx,port),blank,port),arr(infer(ctx,port),port,blank))
    wrapped = comp2(ctx,2,comp2(ctx,2,v(7),place(inside)),v(8))
    check_ctx(ctx)
    target = point+(scalar,arr(scalar,empty,v(1)),arr(scalar,v(1),empty))
    images = [v(0),u,v(1),v(2),v(3)]
    for ty in ctx[5:]:
        _,_,s,t = subst_ty(ty,images)
        images.append(head(point,s,t))
    for i,ty in enumerate(ctx):
        assert infer(target,images[i])==subst_ty(ty,images[:i])
    projected = subst_tm(wrapped,images)
    expected = subst_ty(infer(ctx,wrapped),images)
    assert infer(target,projected)==expected
    if directory:
        emitter = Emitter()
        emitter.check_type('insideCaps',ctx,wrapped,infer(ctx,wrapped))
        emitter.check_type('scalarCapsAtCollapsedEnds',target,projected,expected)
        emitter.check_type('collapsedOpening',target,images[7],subst_ty(ctx[7],images))
        (directory/'PocketChain.agda').write_text(emitter.module('PocketChain',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--blank-ends',action='store_true',help='return the scalar test for arbitrary interior schedules with empty ends')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        print(json.dumps(blank_end_test(data) if args.blank_ends else analyze(data),indent=2))
    else:
        audit()
        typed(args.agda_dir)
