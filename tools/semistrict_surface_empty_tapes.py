"""Build the wired point-end reduction and replay accepting tape programs.

Input JSON: states, instructions ([state,read,target,write,L-or-R]), start,
scanned, and optional left/right symbol lists over a and _. A missing
instruction halts. With --steps N also replay up to N rewrites; exhausting
that bound does not decide nontermination. With --link, the clean tape releases
two identical point gates. Optional pairs and plat_braid in the input place a
signed braid between all releases and the pair closures.
"""
from argparse import ArgumentParser
import json
from pathlib import Path

from semistrict_surface_configuration_braids import BIRTH,CLEAN,DEATH,SYMBOLS,encode,head,rules
from semistrict_surface_birth_death_packets import follow
from semistrict_surface_gate_forests import cable
from semistrict_surface_serial_gate_tracks import read_track


def compile_tape(data):
    states = data['states']
    program = {}
    for q,c,target,write,side in data['instructions']:
        if (q,c) in program or q not in states or target not in states or c not in SYMBOLS or write not in SYMBOLS or side not in ('L','R'):
            raise ValueError('invalid machine instruction')
        program[q,c] = target,write,side
    left,right = tuple(data.get('left',[])),tuple(data.get('right',[]))
    if data['start'] not in states or any(c not in SYMBOLS for c in (*left,data['scanned'],*right)):
        raise ValueError('invalid input tape')
    initial = encode(left,data['start'],data['scanned'],right)
    return initial,rules(states,program)


def explore(initial,table,limit):
    if limit<0:
        raise ValueError('step bound must be nonnegative')
    word = initial
    steps = []
    while word!=(BIRTH,CLEAN,DEATH) and len(steps)<limit:
        match = next(((i,a,b) for a,b in table for i in range(len(word)-len(a)+1)
                      if word[i:i+len(a)]==a),None)
        if match is None:
            raise ValueError('malformed tape encountered')
        i,a,b = match
        steps.append(match)
        word = word[:i]+b+word[i+len(a):]
    return steps,word


LINK_GATES = ('ring-gate',)*2


def replay(initial,steps,copies,twist,link=False,plat_braid=()):
    # Each tape is read bottom-to-top in a separate block. Addresses
    # survive a signed exchange of complete blocks and every untouched seam.
    ports = {}
    live = [[] for _ in range(copies)]
    charts,seams = [],[]
    def boundary(symbol):
        if symbol in LINK_GATES:
            return '',''
        return ('','a') if symbol==BIRTH else ('a','') if symbol==DEATH else ('a','a')
    def change(owner,offset,old,new,ends):
        i = len(charts)
        site = 'u'+str(i)
        ports[site] = ends
        tokens = []
        for j,symbol in enumerate(new):
            name = f'w{i}_{j}'
            ports[name] = boundary(symbol)
            tokens.append((name,symbol))
        if charts:
            seams.append([])
        block = live[owner]
        before = [name for tape in live[:owner] for name,_ in tape]+[g for g,_ in block[:offset]]
        after = [g for g,_ in block[offset+len(old):]]+[name for tape in live[owner+1:] for name,_ in tape]
        taken = block[offset:offset+len(old)]
        assert tuple(g for _,g in taken)==tuple(old)
        rows = lambda ids:[(0,g) for g in ids]
        charts.append(dict(diagram=rows([*before,site,*after]),slot=len(before),
                           input=rows([g for g,_ in taken]),output=rows([g for g,_ in tokens])))
        block[offset:offset+len(old)] = tokens
    for owner in range(copies):
        change(owner,0,(),initial,('',''))
    if twist:
        assert copies==2
        word = cable(twist,[len(tape) for tape in live])
        old = tuple((0,g) for tape in live for g,_ in tape)
        reached = follow(old,word,ports)
        if len(twist)%2:
            live.reverse()
        assert reached==tuple((0,g) for tape in live for g,_ in tape)
    for owner in range(copies):
        for i,a,b in steps:
            change(owner,i,a,b,(boundary(a[0])[0],boundary(a[-1])[1]))
        change(owner,0,(BIRTH,CLEAN,DEATH),LINK_GATES if link else (),('',''))
    if link:
        from semistrict_surface_plat_probes import presentation
        presentation(copies,plat_braid)
        flat = tuple((0,g) for block in live for g,_ in block)
        order = follow(flat,plat_braid,ports)
        for i in range(copies):
            live[i] = [(g,LINK_GATES[0]) for _,g in order[2*i:2*i+2]]
        gap = len(charts)-1
        for owner in range(copies):
            change(owner,0,LINK_GATES,(),('',''))
        seams[gap] = list(plat_braid)
    if twist:
        seams[copies-1] = word
    d = dict(vertex='x',path='',edges={'a':['x','x']},gates={g:['x',s,t] for g,(s,t) in ports.items()},
             charts=charts,seams=seams)
    read_track(dict(d,charts=[dict(c,loop=()) for c in charts]),require_shared_gate=False)
    return d


def run(data,limit=None,link=False):
    initial,table = compile_tape(data)
    result = dict(opening=[[],initial],updates=table,closing=[(BIRTH,CLEAN,DEATH),LINK_GATES if link else []])
    if link:
        result['ring_closing'] = [LINK_GATES,[]]
    if limit is not None:
        steps,last = explore(initial,table,limit)
        result['last_tape'] = last
        result['accepting_program_found'] = last==(BIRTH,CLEAN,DEATH)
        if result['accepting_program_found']:
            copies = data.get('pairs',1) if link else 1
            braid = data.get('plat_braid',()) if link else ()
            result['movie'] = replay(initial,steps,copies,(),link,braid)
    return result


def typed(directory):
    from catt import STAR,arr,check_ctx,comp2,infer,subst_tm,subst_ty,v
    from emit_agda import Emitter
    from relative_coherence_hidden_seam import identity
    from semistrict_surface_event_holes import scalar_images

    ctx = (STAR,arr(STAR,v(0),v(0)))
    u = identity(ctx,v(0))
    a = v(1)
    def ty(s,t):
        return arr(infer(ctx,s),s,t)
    ctx += (ty(u,a),ty(a,u),ty(a,a),ty(a,a))
    def tape(h):
        return comp2(ctx,1,comp2(ctx,1,v(2),h),v(3))
    e = identity(ctx,u)
    ctx += (ty(e,tape(v(4))),ty(v(4),v(5)),ty(tape(v(5)),e))
    check_ctx(ctx)
    p = comp2(ctx,2,comp2(ctx,2,v(6),tape(v(7))),v(8))
    end = ty(e,e)
    assert infer(ctx,p)==end
    two = comp2(ctx,2,p,p)
    target,images = scalar_images(ctx,[6])
    seen = subst_tm(two,images)
    assert infer(target,seen)==subst_ty(end,images)
    if directory:
        emitter = Emitter()
        emitter.check_type('emptyToEmptyTape',ctx,p,end)
        emitter.check_type('twoAcceptingTapes',ctx,two,end)
        emitter.check_type('readBothOpenings',target,seen,subst_ty(end,images))
        (directory/'EmptyTapeReturn.agda').write_text(emitter.module('EmptyTapeReturn',__doc__.splitlines()[0]))

    # Same prepared tape and update, but release the two cap occurrences.
    ctx = ctx[:8]+(infer(ctx,e),)
    pair = comp2(ctx,1,v(8),v(8))
    ctx += (ty(tape(v(5)),pair),ty(pair,e))
    check_ctx(ctx)
    birth = comp2(ctx,2,comp2(ctx,2,v(6),tape(v(7))),v(9))
    closed = comp2(ctx,2,birth,v(10))
    assert infer(ctx,birth)==ty(e,pair) and infer(ctx,closed)==end
    # Flatten the wired part, retaining the actual release and pair closure
    # at the images of their written ports (including the old tape fits).
    target,images = scalar_images(ctx[:8],[])
    for i in range(8,11):
        decl = subst_ty(ctx[i],images)
        target += (decl,)
        images.append(v(len(target)-1))
    check_ctx(target)
    projected = subst_tm(closed,images)
    assert infer(target,projected)==subst_ty(end,images)
    if directory:
        emitter = Emitter()
        emitter.check_type('acceptingTapeAsPairBirth',ctx,birth,ty(e,pair))
        emitter.check_type('closedWiredPair',ctx,closed,end)
        emitter.check_type('retainBothCapRules',target,projected,subst_ty(end,images))
        (directory/'LinkedTapeReturn.agda').write_text(emitter.module('LinkedTapeReturn',__doc__.splitlines()[0]))


def audit():
    from semistrict_surface_configuration_braids import check_transitions
    from semistrict_surface_spherical_relations import analyze as spheres
    from semistrict_surface_plat_probes import decide

    check_transitions()
    data = dict(states=['s','t','h'],start='s',scanned='_',instructions=[
        ['s','_','t','a','R'],['t','_','h','a','L']])
    initial,table = compile_tape(data)
    steps,word = explore(initial,table,20)
    assert word==(BIRTH,CLEAN,DEATH)
    for copies,twist in [(1,()),(2,(1,)),(2,(-1,-1)),(3,())]:
        movie = replay(initial,steps,copies,twist)
        r = spheres(movie)
        assert r['betti']==[1,0,copies] and r['sphere_orbits']==copies
        linked = spheres(replay(initial,steps,copies,twist,True))
        assert linked['betti']==[1,copies,copies]
    for braid,components,fills in [([2],1,True),([2,2],2,True),([2,2,2],1,False),([-2]*3,1,False)]:
        movie = run(dict(data,pairs=2,plat_braid=braid),20,True)['movie']
        seam = movie['seams'][-2]
        assert seam==braid and spheres(movie)['betti']==[1,components,components]
        answer = decide(dict(pairs=2,braid=seam,word=[1,2,-1,-2]))
        assert answer['raw_filler']==fills
    loop = dict(data,states=['s'],instructions=[['s','_','s','_','R']])
    answer = run(loop,30)
    assert not answer['accepting_program_found'] and len(answer['last_tape'])==33
    print('one, two, and three accepting tapes replay; signed whole-tape exchanges preserve the independent probe counts')
    print('Linked tape releases replay on four signed plats; their actual seam distinguishes both trefoil commutators.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--steps',type=int)
    parser.add_argument('--link',action='store_true',help='release two point gates at acceptance and close them together')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(run(json.loads(args.input.read_text()),args.steps,args.link),indent=2))
    else:
        audit()
        typed(args.agda_dir)
