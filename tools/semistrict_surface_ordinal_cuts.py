"""Find compulsory cuts and test endpoint exceptions in a serial ordinary 3-movie.

Input uses the serial gate-tracks JSON. Reported blocks are ordered by actual
gate dependence, including occurrences of the same colour exchanged at seams.
--paths also emits full incidence paths through a connected-port middle.
"""
from argparse import ArgumentParser
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_component_braids import Partition
from semistrict_surface_gate_forests import Presentation, cable
from semistrict_surface_movie_spine import expanded
from semistrict_surface_port_angles import inspect
from semistrict_surface_probe_movies import Faces
from semistrict_surface_scalar_leaves import gate_segments
from semistrict_surface_serial_gate_tracks import read_track


def blocks_for(steps,sources):
    ancestors = []
    for _,ins,_,_ in steps:
        pred = {sources[g] for g in ins if sources[g] is not None}
        ancestors.append(pred.union(*(ancestors[p] for p in pred)))
    parts = Partition()
    for j,earlier in enumerate(ancestors):
        for i in range(j):
            if i not in earlier:
                parts.unite(i,j)
    groups = {}
    for i in range(len(steps)):
        groups.setdefault(parts.at(i),[]).append(i)
    return list(groups.values())


def middle_paths(steps,initial,final):
    prefixes = {g:[(g,)] for g in initial}
    for _,inputs,outputs,_ in steps:
        old = [p for g in inputs for p in prefixes.pop(g)]
        for g in outputs:
            prefixes[g] = [(*p,g) for p in old]
    assert set(prefixes)==set(final)
    return [p for g in final for p in prefixes[g]]


def classify(data,show_paths=False):
    initial,final,sources,_,steps = gate_segments(data)
    blocks = blocks_for(steps,sources)
    model = Presentation(dict(data,rules={},diagram=[]))
    charts = data['charts']
    roles = []
    holes = {}
    for i,c in enumerate(charts):
        slot = c['slot']
        offset,site = c['diagram'][slot]
        if all(inspect(model,site,c[side]) for side in ('input','output')):
            roles.append('positive')
        elif bool(c['input'])!=bool(c['output']):
            side,kind = ('input','birth') if c['output'] else ('output','death')
            v,s,t = model.gates[site]
            assert s==t
            roles.append(kind)
            if s:
                holes[i] = 0
            else:
                # Name positions rather than colours for the nesting calculation.
                rows = expanded(c,side)
                marked = [(p,j) for j,(p,_) in enumerate(rows)]
                ports = {j:model.ports[g] for j,(_,g) in enumerate(rows)}
                faces = Faces(marked,ports,len(data['path']))
                holes[i] = faces.holes[faces.spots[slot,offset]]
        else:
            roles.append('other')
    result = dict(blocks=blocks,roles=roles,forced_regular_gaps=[g[-1]+1 for g in blocks[:-1]])
    # One-site blocks always have 1-type coefficients, even with bad ports.
    result['certifies_all_raw_from_six'] = all(len(g)==1 or all(roles[i]=='positive' for i in g) for g in blocks)
    isolated = all(roles[i]=='positive' or (len(g)==1 and roles[i] in ('birth','death'))
                   for g in blocks for i in g)
    if not isolated:
        return result
    birth = roles[0]=='birth'
    death = roles[-1]=='death'
    assert roles.count('birth')==int(birth) and roles.count('death')==int(death)
    result['degree_five_reduces_to_one_mixed_probe'] = True
    result['endpoint_kernel_ranks'] = [holes.get(0,0) if birth else 0,holes.get(len(steps)-1,0) if death else 0]
    left = (steps[0][0]+steps[0][2]+steps[0][3]) if birth else initial
    right = (steps[-1][0]+steps[-1][1]+steps[-1][3]) if death else final
    # Reachability suffices for the decision. Enumerate potentially exponential
    # paths only on explicit request for the cabling certificate.
    from_birth = set(steps[0][2]) if birth else set()
    from_initial = set(initial)
    middle = steps[int(birth):len(steps)-int(death)]
    for _,ins,outs,_ in middle:
        if from_birth.intersection(ins):
            from_birth.update(outs)
        if from_initial.intersection(ins):
            from_initial.update(outs)
    absorbed = death and bool(from_initial.intersection(steps[-1][1]))
    escaped = bool(from_birth.intersection(final))
    result['initial_to_death'] = absorbed
    result['birth_to_final'] = escaped
    result['certifies_all_raw_from_five'] = min(result['endpoint_kernel_ranks'])==0 or absorbed or escaped
    if show_paths:
        result['middle_paths'] = middle_paths(middle,left,right)
    return result


def diamond(order,wired=False,spectator=False):
    defs = {}
    charts = []
    def add(label,s,t):
        defs[label] = ['x',s,t]
        return label
    def rows(names):
        return [(0,n) for n in names]
    live = []
    if wired or spectator:
        live = [add('b','', 'f'),add('d','f','')]
    def change(slot,old,new,s,t):
        assert live[slot:slot+len(old)]==old
        marker = add('site'+str(len(charts)),s,t)
        charts.append(dict(diagram=rows(live[:slot]+[marker]+live[slot+len(old):]),
                           slot=slot,input=rows(old),output=rows(new)))
        live[slot:slot+len(old)] = new
    if wired:
        m = add('m','ff','f')
        s = add('s','f','ff')
        change(1,[],[m,s],'ff','ff')
        starts = [['b',m],[s,'d']]
        widths = [('f','f'),('f','f')]
        ends = [[add('l','f','f')],[add('r','f','f')]]
    else:
        b = add('ib','','f')
        d = add('id','f','')
        change(0,[],[b,d],'','')
        starts = [[b],[d]]
        widths = [('','f'),('f','')]
        ends = [[add('b2','','f'),add('lh','f','f')],[add('rh','f','f'),add('d2','f','')]]
    visits = [0,0]
    for who in order:
        a,b = starts[who],ends[who]
        if visits[who]:
            a,b = b,a
        change(live.index(a[0]),a,b,*widths[who])
        visits[who] += 1
    assert visits==[2,2]
    if wired:
        change(1,['m','s'],[],'ff','ff')
    else:
        change(0,['ib','id'],[],'','')
    result = dict(vertex='x',edges={'f':['x','x']},path='f' if wired else '',gates=defs,
                  charts=charts,seams=[[] for _ in charts[1:]])
    for c in charts:
        c['loop'] = cable((1,1),[len(c['diagram'])-2,2]) if spectator and not wired else []
    return result


def audit():
    for positions in combinations(range(4),2):
        order = [int(i in positions) for i in range(4)]
        for wired,spectator in [(False,False),(True,False),(False,True)]:
            data = diamond(order,wired,spectator)
            result = classify(data,True)
            assert result['blocks']==[[0],[1,2,3,4],[5]]
            assert result['certifies_all_raw_from_six'] and result['certifies_all_raw_from_five']==(not spectator)
            assert len(result['middle_paths'])==(8 if wired else 4+2*int(spectator))
            # On the two scalar caps the whole active disk winds once around
            # an exterior stationary interval. Test the actual cabled site
            # braids, both fixed ends and every intermediate seam equation.
            assert read_track(data,require_shared_gate=False)['nonzero']==spectator
    from semistrict_surface_scalar_leaves import sample
    absorbed = sample(['left','hole'],[(0,0,1),(0,2,1),(0,1,0)],[[],[]])
    escaped = sample(['hole'],[(0,0,1),(0,1,2),(0,1,0)],[[],[]])
    for data,flag in [(absorbed,'initial_to_death'),(escaped,'birth_to_final')]:
        result = classify(data,True)
        assert min(result['endpoint_kernel_ranks'])>0 and result[flag] and result['certifies_all_raw_from_five']
    point = sample([],[(0,0,2),(0,0,2),(0,2,0),(0,2,0)],[[],[],[]])
    assert classify(point)['blocks']==[[0,1,2,3]] and not classify(point)['certifies_all_raw_from_six']
    seam = sample([],[(0,0,1),(1,0,1),(0,1,0),(0,1,0)],[[],[-1],[]])
    _,_,sources,targets,_ = gate_segments(seam)
    assert list(zip(sources,targets))==[(0,3),(1,2)]
    print('Checked all six orders of each of three branching middles, their cabled loops and a signed-seam change of incidences.')


def typed(directory):
    from catt import comp2,glue_tree,infer,maximal_vars,src,tgt,tree_ctx,v
    from emit_agda import Emitter
    from relative_coherence_exchange_faces import head
    from semistrict_surface_box_exceptions import rules
    from semistrict_surface_box_ports import fixed_context,raw_hom,raw_row
    from semistrict_surface_directed_power_queries import apply

    ctx,_,inst,_ = fixed_context(rules)
    arity = tree_ctx(glue_tree(3,1,3))
    a,b = map(v,maximal_vars(arity))
    def ordered(c,p,q,swap=False):
        if swap:
            steps = comp2(c,1,src(c,p),q),comp2(c,1,p,tgt(c,q))
        else:
            steps = comp2(c,1,p,src(c,q)),comp2(c,1,tgt(c,p),q)
        return comp2(c,2,*steps)
    native = head(arity,ordered(arity,a,b),ordered(arity,a,b,True))
    l,r = inst['leaf-b',False],inst['leaf-d',False]
    switch = apply(ctx,(arity,native),[l,r])
    restore = ordered(ctx,inst['leaf-b',True],inst['leaf-d',True])
    def close(cell):
        return raw_row(ctx,2,[inst['empty-seed',False],cell,restore,inst['empty-seed',True]])
    exchange = close(switch)
    typ = raw_hom(ctx,close(ordered(ctx,l,r)),close(ordered(ctx,l,r,True)))
    assert infer(ctx,exchange)==typ
    if directory:
        emitter = Emitter()
        emitter.check_type('exchangeBetweenCompulsoryCaps',ctx,exchange,typ)
        (directory/'OrdinalCaps.agda').write_text(emitter.module('OrdinalCaps',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--paths',action='store_true')
    parser.add_argument('--sample',choices=('empty','spectator','wired'))
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.sample:
        print(json.dumps(diamond([0,1,1,0],wired=args.sample=='wired',spectator=args.sample=='spectator'),indent=2))
    elif args.input:
        print(json.dumps(classify(json.loads(args.input.read_text()),args.paths),indent=2))
    else:
        audit()
        typed(args.agda_dir)
