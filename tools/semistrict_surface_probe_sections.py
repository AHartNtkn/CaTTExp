"""Place named scalar probes at the initial cut or inside an output occurrence.

Uses serial probe_movies JSON. 'probes' lists the named placements in order;
the returned program inserts them into the indicated local gate lists. Each
entry is one extra temporal step, with identical 2-faces on erasure.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, subst_tm, subst_ty, v
from catt import disc_tree, glue_tree, maximal_vars, sub_from, tdim_tm, tree_ctx
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from relative_coherence_exchange_faces import head
from semistrict_surface_birth_death_packets import expand, expand_path, follow
from semistrict_surface_component_braids import restrict
from semistrict_surface_gate_forests import Presentation
from semistrict_surface_probe_movies import configuration_betti, movie
from semistrict_surface_serial_gate_tracks import read_track
from semistrict_surface_shared_edge import braid_image


def section(data):
    components = movie(data)
    by_probe = {i:c for c in components for i in c['probe_indices']}
    charts = data['charts']
    source = charts[0]
    def full(c,side):
        i = c['slot']
        p,site = c['diagram'][i]
        return [*c['diagram'][:i],*[(p+q,g) for q,g in c[side]],*c['diagram'][i+1:]]
    model = Presentation(dict(data,diagram=full(source,'input'),rules={}))
    result,insertions = [],{}
    gates = dict(data['gates'])
    for i in sorted(by_probe):
        component = by_probe[i]
        place = component['section']
        row,pos = place['spot']
        use = place.get('use')
        if use is None:
            rows = full(source,'input')
            x,s = data['vertex'],data['path']
            gap = 0
        else:
            chart = charts[use]
            outer,site = chart['diagram'][chart['slot']]
            x,s,_ = gates[site]
            rows = chart['output']
            gap = use+1
        path = model.sweep(x,s,rows[:row])
        obj = model.end(x,path[:pos])
        uid = f'probe_{i}'
        while uid in gates:
            uid += '_'
        gates[uid] = [obj,'','']
        result.append(dict(name=i,component=component['component'],object=obj,**place))
        if use is not None:
            row,pos = row+chart['slot'],pos+outer
            rows = full(chart,'output')
        # The two empty ports of the added step leave its old cut literal.
        extra = dict(diagram=[*rows[:row],(pos,uid),*rows[row:]],slot=row,input=[],output=[])
        insertions.setdefault(gap,[]).append(extra)
    # Validate the entire marked schedule, including the old seam after each
    # run of local insertions and distinct probe names inside the same face.
    marked,seams = [],[]
    for gap in range(len(charts)+1):
        batch = list(insertions.get(gap,[]))
        if gap<len(charts):
            batch.append(charts[gap])
        for c in batch:
            if marked:
                # The old seam leads into the next structural chart.
                seams.append(data['seams'][gap-1] if gap and gap<len(charts) and c is charts[gap] else [])
            marked.append(c)
    read_track(dict(data,gates=gates,charts=[dict(c,loop=()) for c in marked],seams=seams),
               require_shared_gate=False)
    return result


def lens():
    gates = dict(H=['x','',''],b=['x','','ab'],d=['x','ab',''],s=['y','',''])
    return dict(vertex='x',path='',edges={'a':['x','y'],'b':['y','x']},gates=gates,
                charts=[dict(diagram=[(0,'H')],slot=0,input=a,output=b)
                        for a,b in [([],[(0,'b'),(1,'s'),(0,'d')]),
                                    ([(0,'b'),(1,'s'),(0,'d')],[])]],seams=[[]])


def audit():
    base = lens()
    # The same birth/death declarations fire twice. The probes are at the
    # same local address but in different temporal components.
    repeated = dict(base,charts=base['charts']*2,seams=[[],[],[]],
                    probes=[[1,1,1],[3,2,1],[1,2,1],[2,0,0]])
    result = section(repeated)
    assert [r.get('use') for r in result]==[0,2,0,None]
    assert [r['object'] for r in result]==['y','y','y','x']
    assert result[0]['component']==result[2]['component']!=result[1]['component']

    # Input and output of a wired site: an internal pocket between a split
    # and merge. Its written coordinates differ from those in the whole cut.
    gates = dict(J=['x','a','a'],F=['x','a','aa'],M=['x','aa','a'],z=['x','a','a'])
    block = [(0,'F'),(0,'M')]
    charts = [dict(diagram=[(0,'z'),(1,'J')],slot=1,input=a,output=b)
              for a,b in [([],block),(block,[])]]
    wired = dict(vertex='x',path='aaa',edges={'a':['x','x']},gates=gates,charts=charts,
                 seams=[[]],probes=[[1,2,2]])
    received, = section(wired)
    assert received['use']==0 and received['spot']==[1,1]

    # Two structural point events in an ungraded transient pocket. A third
    # point is the probe. On erasure it can still be attached to the opening.
    pocket_gates = dict(J=['x','aa','aa'],F=['x','a','aa'],M=['x','aa','a'],H=['x','',''])
    pocket = [(1,'F'),(1,'M')]
    middle = dict(diagram=[pocket[0],(2,'H'),pocket[1]],slot=1,input=[],output=[])
    opened = dict(diagram=[(0,'J')],slot=0,input=[],output=pocket)
    closed = dict(diagram=[(0,'J')],slot=0,input=pocket,output=[])
    history = dict(vertex='x',path='aa',edges={'a':['x','x']},gates=pocket_gates,
                   charts=[opened,middle,middle,closed],seams=[[],[],[]],probes=[[3,1,2]])
    anchor, = section(history)
    assert anchor['use']==0 and anchor['spot']==[1,2]
    punctures = configuration_betti(1,[1,1,2],lambda x,y,t:x==y==1 and t in (1,3))
    base_points = configuration_betti(2,[0,0,0],lambda *_:False)
    total_points = configuration_betti(3,[0,0,0],lambda *_:False)
    assert (punctures[2],base_points[2],total_points[2])==(2,1,3)
    print('temporary wired pocket: second Betti ranks 2 in the fibre, 1 in the base, 3 in the total')

    # Two moving site disks and an exterior spectator. Decorate each output
    # with a scalar at its internal face, cable a signed joint seam, then
    # forget the two inserted strands and compare to the undecorated motion.
    diagrams = ((0,'A'),(0,'B'),(0,'z'))
    ports = {g:('','') for g in ('A','B','z')}
    bare,more = {},{}
    for k in ('A','B'):
        ports.update({k+'b':('','ab'),k+'d':('ab',''),k+'s':('','')})
        bare[k] = [(0,k+'b'),(0,k+'d')]
        more[k] = [(0,k+'b'),(1,k+'s'),(0,k+'d')]
    checks = switches = 0
    for size in range(5):
        for word in product((1,-1,2,-2),repeat=size):
            end = follow(diagrams,word,ports)
            initial = expand(diagrams,more)
            path = expand_path(diagrams,word,more)
            assert follow(initial,path,ports)==expand(end,more)
            keep = {i for i,(_,g) in enumerate(initial) if g not in ('As','Bs')}
            underlying = restrict(len(initial),path,keep)
            assert braid_image(len(keep),underlying)==braid_image(len(keep),expand_path(diagrams,word,bare))
            switches += len(path)
            checks += 1
    print('temporary point and wired faces recovered at their actual output rows; repeated uses separated')
    print(f'{checks} decorated joint seams, {switches} legal signed switches, all erase to the prescribed braid')


def typed(directory):
    ctx = (STAR,STAR,arr(STAR,v(0),v(1)),arr(STAR,v(1),v(0)))
    def hom(s,t):
        return arr(infer(ctx,s),s,t)
    x,y,a,b = (v(i) for i in range(4))
    unit = identity(ctx,x)
    blank = identity(ctx,identity(ctx,y))
    ctx += (hom(blank,blank),)
    inner = comp2(ctx,0,comp2(ctx,0,a,v(4)),b)
    _,_,cross,_ = infer(ctx,inner)
    _,_,path,_ = infer(ctx,cross)
    ctx += (hom(unit,path),hom(path,unit))
    pocket = comp2(ctx,1,comp2(ctx,1,v(5),inner),v(6))
    _,_,port,other = infer(ctx,pocket)
    assert port==other
    empty = identity(ctx,unit)
    ctx += (hom(empty,port),hom(port,empty))
    check_ctx(ctx)
    decorated = comp2(ctx,2,v(7),pocket)
    assert infer(ctx,decorated)==infer(ctx,v(7))
    close = comp2(ctx,2,decorated,v(8))
    plain = comp2(ctx,2,v(7),v(8))
    history = comp2(ctx,2,plain,close)
    assert infer(ctx,history)==hom(empty,empty)
    erase = [v(i) if i!=4 else identity(ctx,blank) for i in range(len(ctx))]
    for i,ty in enumerate(ctx):
        assert infer(ctx,erase[i])==subst_ty(ty,erase[:i])
    erased = subst_tm(history,erase)
    # Normalize the erased parked probe through its four written whiskers.
    # Each identity-composition comparison lives on its own generic arity.
    original = blank
    compare = None
    for cut,side,fixed in [(0,1,a),(0,0,b),(1,1,v(5)),(1,0,v(6))]:
        args = [fixed,fixed]
        args[side] = original
        arity = tree_ctx(glue_tree(tdim_tm(ctx,args[0]),cut,tdim_tm(ctx,args[1])))
        variables = maximal_vars(arity)
        abstract = list(map(v,variables))
        ordinary = comp2(arity,cut,*abstract)
        fitted = abstract.copy()
        fitted[side] = identity(arity,abstract[side])
        local = head(arity,comp2(arity,cut,*fitted),identity(arity,ordinary))
        law = subst_tm(local,sub_from(arity,ctx,dict(zip(variables,args))))
        if compare is not None:
            lifted = args.copy()
            lifted[side] = compare
            law = comp2(ctx,3,comp2(ctx,cut,*lifted),law)
        original,compare = comp2(ctx,cut,*args),law
    assert original==port and infer(ctx,compare)==hom(subst_tm(pocket,erase),identity(ctx,port))
    disc = tree_ctx(disc_tree(3))
    g, = map(v,maximal_vars(disc))
    right_unit = head(disc,comp2(disc,2,g,identity(disc,infer(disc,g)[3])),g)
    unit_fit = subst_tm(right_unit,sub_from(disc,ctx,{maximal_vars(disc)[0]:v(7)}))
    erase_fit = comp2(ctx,3,comp2(ctx,2,v(7),compare),unit_fit)
    assert infer(ctx,erase_fit)==hom(subst_tm(decorated,erase),v(7))
    if directory:
        out = Emitter()
        out.check_type('secondBirthWithInteriorProbe',ctx,history,hom(empty,empty))
        out.check_type('erasedSecondBirth',ctx,erased,hom(empty,empty))
        out.check_type('erasureAtTheWrittenBirth',ctx,erase_fit,hom(subst_tm(decorated,erase),v(7)))
        (directory/'ProbeSections.agda').write_text(out.module('ProbeSections',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(section(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
        typed(args.agda_dir)
