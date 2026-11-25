"""Compute the birth configurations of connected components at empty written ends.

Read the named serial gate-track format. A blank port is allowed only at a
point site. Each nonblank port must be one connected graph spanning its rim.
"""
from argparse import ArgumentParser
from itertools import combinations
import json
from math import comb
from pathlib import Path

from semistrict_surface_component_braids import Components
from semistrict_surface_gate_forests import Presentation, cable
from semistrict_surface_movie_spine import expanded
from semistrict_surface_port_angles import inspect
from semistrict_surface_probe_movies import movie
from semistrict_surface_serial_gate_tracks import motion


def classify(data):
    charts = data['charts']
    if not charts:
        if data['path'] or data.get('diagram')!=[] or data['seams']:
            raise ValueError('a stationary movie needs its explicit empty drawing and no seams')
        return dict(groups=[],degree_six_rank=0)
    if data['path'] or expanded(charts[0],'input') or expanded(charts[-1],'output'):
        raise ValueError('both ends must be the empty drawing on the empty path')
    model = Presentation(dict(data,diagram=[],rules={}))
    for c in charts:
        site = c['diagram'][c['slot']][1]
        _,s,t = model.gates[site]
        if not c['input'] and not c['output']:
            raise ValueError('free point with two blank ports')
        for side in ('input','output'):
            block = c[side]
            port = inspect(model,site,block)
            if not block:
                eligible = not s and not t
            elif s or t:
                eligible = port is not None and len(port['core'])==len(block)
            else:
                eligible = len(Components(block,model.ports,0).skeleton)==1
            if not eligible:
                raise ValueError('port needs a single spanning graph or a point-site cap')
    regions = movie(data,with_births=True)
    groups = [dict(host=c['section'],births=c['births']) for c in regions if c['births']]
    return dict(groups=groups,degree_six_rank=sum(comb(len(g['births']),2) for g in groups))


def lens_movie(pattern,twist=False,wire_pairs=0,close_with_positive_ports=False):
    """One root with successive lenses; insert the indicated siblings in each."""
    ports = {'b':('','f'),'d':('f',''),'h':('f','f'),'s':('f','ff'),'m':('ff','f')}
    gates,charts,seams,rows = {},[],[],[]
    pending = ()
    def change(slot,p,old,new,s,t):
        nonlocal pending
        marker = 'site'+str(len(charts))
        gates[marker] = ['x',s,t]
        before = [(0,g) for g in old]
        assert rows[slot:slot+len(old)]==[(p,g) for g in old]
        after = []
        for colour in new:
            g = colour+str(len(gates))
            gates[g] = ['x',*ports[colour]]
            after.append((0,g))
        charts.append(dict(slot=slot,diagram=rows[:slot]+[(p,marker)]+rows[slot+len(old):],
                           input=before,output=after,loop=[]))
        if len(charts)>1:
            seams.append(pending)
        pending = ()
        rows[slot:slot+len(old)] = [(p,g) for _,g in after]
        return [g for _,g in after]
    a,z = change(0,0,[],'bd','','')
    change(2,0,[],'bd','','')
    def index(g):
        return next(i for i,(_,name) in enumerate(rows) if name==g)
    if twist:
        pending = cable((1,),[2,2])
        rows = list(motion(tuple(rows),{g:(s,t) for g,(_,s,t) in gates.items()},pending))
    a,h = change(index(a),0,[a],'bh','','f')
    for count in pattern:
        s,m = change(index(h),0,[h],'sm','f','f')
        for _ in range(wire_pairs):
            pair = change(index(m),0,[],'ms','ff','ff')
            change(index(m)-2,0,pair,'','ff','ff')
        children = [change(index(m),1,[],'bd','','') for _ in range(count)]
        for b,d in children:
            change(index(b),1,[b,d],'','','')
        if close_with_positive_ports:
            merge,split = change(index(m),0,[],'ms','ff','ff')
            lower, = change(index(s),0,[s,merge],'h','f','f')
            upper, = change(index(split),0,[split,m],'h','f','f')
            h, = change(index(lower),0,[lower,upper],'h','f','f')
        else:
            h, = change(index(s),0,[s,m],'h','f','f')
    a, = change(index(a),0,[a,h],'b','','f')
    change(index(a),0,[a,z],'','','')
    change(0,0,[g for _,g in rows],'','','')
    return dict(vertex='x',edges={'f':['x','x']},path='',gates=gates,charts=charts,seams=seams)


def audit():
    from semistrict_surface_ordinal_cuts import diamond
    from semistrict_surface_scalar_leaves import sample
    for pattern in [(2,),(1,1),(3,1,0)]:
        for twist in (False,True):
            data = lens_movie(pattern,twist)
            result = classify(data)
            assert [len(g['births']) for g in result['groups']]==[2,*filter(bool,pattern)]
            assert result['degree_six_rank']==1+sum(comb(n,2) for n in pattern)
            # Independent one-probe calculation: each complete floating
            # sibling is one bounded obstacle in precisely its own host.
            homology = movie(data,with_homology=True)
            assert [f['betti'] for f in homology]==[[1,0,n] for n in (2,*pattern)]
    for left in combinations(range(4),2):
        result = classify(diamond([int(i in left) for i in range(4)]))
        assert result['degree_six_rank']==0 and result['groups'][0]['births']==[0]
    assert classify(dict(path='',diagram=[],charts=[],seams=[]))['groups']==[]
    for excluded in (lens_movie([1],wire_pairs=1),sample([],[(0,0,2),(0,2,0)],[[]])):
        movie(excluded)
        try:
            classify(excluded)
        except ValueError as err:
            assert 'single spanning graph' in str(err)
        else:
            raise AssertionError('accepted a two-wire cap or a disconnected port')
    print('Checked six branched schedules and six nested movies, including signed seams, distinct lens lifetimes and independent obstacle counts.')


def typed(directory):
    from catt import comp2,glue_tree,infer,maximal_vars,src,subst_tm,tgt,tree_ctx,v
    from emit_agda import Emitter
    from relative_coherence_exchange_faces import head
    from relative_coherence_hidden_seam import identity
    from semistrict_surface_box_exceptions import rules
    from semistrict_surface_box_ports import fixed_context,gates,raw_hom,raw_row
    from semistrict_surface_directed_power_queries import apply

    ctx,read,rule,_ = fixed_context(rules)
    seed,close = (rule['empty-seed',back] for back in (False,True))
    child = comp2(ctx,2,seed,close)
    # Insert that actual return into the empty spatial interval between two
    # wires. Perform every unit change on the generic line before folding.
    line = tree_ctx(((),()))
    f,g = map(v,maximal_vars(line))
    ff = comp2(line,0,f,g)
    def surround(c,a,cell,b):
        return comp2(c,0,comp2(c,0,a,cell),b)
    blank = identity(line,identity(line,tgt(line,f)))
    idle = surround(line,f,blank,g)
    enter,exit = head(line,ff,src(line,idle)),head(line,tgt(line,idle),ff)
    def fit(c,left,term,right):
        return raw_row(c,1,[left,term,right])
    middle = fit(line,enter,idle,exit)
    wire = v(1)
    sigma = [v(0),v(0),wire,v(0),wire]
    active = fit(ctx,subst_tm(enter,sigma),surround(ctx,wire,child,wire),subst_tm(exit,sigma))
    between = raw_row(ctx,2,[subst_tm(head(line,identity(line,ff),middle),sigma),
                             active,subst_tm(head(line,middle,identity(line,ff)),sigma)])
    pair = tree_ctx(glue_tree(2,1,2))
    u,w = map(v,maximal_vars(pair))
    direct = comp2(pair,1,u,w)
    padded = fit(pair,u,identity(pair,tgt(pair,u)),w)
    split,merge = (read(gates[k]) for k in ('s','m'))
    def pair_fit(a,b):
        return apply(ctx,(pair,head(pair,a,b)),[split,merge])
    def rooted_lens(program):
        lens = raw_row(ctx,2,[pair_fit(direct,padded),fit(ctx,split,program,merge),pair_fit(padded,direct)])
        parent = raw_row(ctx,2,[rule['cancel-fork-to-h',True],lens,rule['cancel-fork-to-h',False]])
        # The parent starts as b;d. Its b grows to b;h, and h carries the lens.
        return raw_row(ctx,2,[seed,comp2(ctx,1,rule['leaf-b',False],read(gates['d'])),
                              fit(ctx,read(gates['b']),parent,read(gates['d'])),
                              comp2(ctx,1,rule['leaf-b',True],read(gates['d'])),close])
    rooted = rooted_lens(between)
    barrier = rooted_lens(comp2(ctx,2,rule['wire-pair',False],rule['wire-pair',True]))
    typ = raw_hom(ctx,src(ctx,seed),src(ctx,seed))
    assert infer(ctx,rooted)==infer(ctx,barrier)==typ
    if directory:
        emitter = Emitter()
        emitter.check_type('childInReturningLens',ctx,rooted,typ)
        emitter.check_type('wireBarrierInsideReturningLens',ctx,barrier,typ)
        (directory/'FaceLifetimes.agda').write_text(emitter.module('FaceLifetimes',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--sample',action='store_true')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.sample:
        print(json.dumps(lens_movie([2,1],True),indent=2))
    elif args.input:
        print(json.dumps(classify(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
        typed(args.agda_dir)
