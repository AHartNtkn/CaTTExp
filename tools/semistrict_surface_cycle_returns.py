"""Detect named degree-five obstructions at empty ends of scalar-rule computads.

Use the point_gates/rules JSON of semistrict_surface_empty_returns. With
--witness, return an executable signed movie, a simple incidence cycle and
a specified gate whose meridian links that cycle once.
"""
from argparse import ArgumentParser
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_component_braids import Partition
from semistrict_surface_empty_returns import find_return, movie, return_rules
from semistrict_surface_scalar_leaves import read_edges


def marked_net(data,degrees=(2,)):
    rules = {}
    for name in return_rules(data):
        inputs,outputs = data['rules'][name]
        ports = inputs+outputs
        for degree in (0,*degrees):
            for selected in combinations(range(len(ports)),degree):
                decorated = [(p,i in selected) for i,p in enumerate(ports)]
                rules[name,selected] = decorated[:len(inputs)],decorated[len(inputs):]
    return dict(point_gates=[(p,bit) for p in data['point_gates'] for bit in (False,True)],rules=rules)


def cycle_certificate(drawing,path):
    initial,final,sources,targets,steps = read_edges(drawing)
    assert not initial and not final
    incident = {}
    for i,((_,pair),(_,ins,outs,_)) in enumerate(zip(path,steps,strict=True)):
        if pair:
            incident[i] = [(ins+outs)[j] for j in pair]
    assert all(n==2 for n in Counter(e for pair in incident.values() for e in pair).values())
    event = start = min(incident)
    incoming = None
    walk = []
    while True:
        edge = next(e for e in incident[event] if e!=incoming)
        sign = 1 if sources[edge]==event else -1
        walk.append(dict(event=event,edge=edge,orientation=sign))
        event = targets[edge] if sign==1 else sources[edge]
        if event==start:
            break
        incoming = edge
    assert len({s['event'] for s in walk})==len(walk)
    edge = walk[0]['edge']
    birth = sources[edge]
    below,_,outputs,_ = steps[birth]
    return dict(cycle=walk,meridian=dict(edge=edge,after_event=birth,
                output_cut_position=len(below)+outputs.index(edge),
                linking_number=walk[0]['orientation']))


def analyze(data,witness=False):
    decorated = marked_net(data)
    allowed = return_rules(decorated)
    marked = [g for g in allowed if g[1]]
    result = dict(named_degree_five_obstruction_at_empty_ends=bool(marked))
    if marked and witness:
        path = find_return(decorated,allowed,set(marked))
        # Realize the decorated colours before forgetting them. Pairing by the
        # original colour alone could connect different occurrences.
        drawing = movie(decorated,path)
        result.update(program=[dict(rule=g,marked_ports=pair) for g,pair in path],
                      movie=drawing,**cycle_certificate(drawing,path))
    return result


def component_ranks(drawing):
    initial,final,sources,targets,steps = read_edges(drawing)
    assert not initial and not final
    parts = Partition()
    chords = []
    for edge,(s,t) in enumerate(zip(sources,targets,strict=True)):
        if parts.at(s)==parts.at(t):
            chords.append(edge)
        else:
            parts.unite(s,t)
    groups = {parts.at(i):[] for i in range(len(steps))}
    for e in chords:
        groups[parts.at(sources[e])].append(e)
    return list(groups.values())


def splice_copies(drawing,edge,copies):
    """Rebuild the prescribed incidence graph, cycling the chosen strand."""
    if copies<1:
        raise ValueError('expected a positive copy count')
    _,_,sources,_,steps = read_edges(drawing)
    cut = sources[edge]+1
    schedule = [(i,j) for block in (range(cut),range(cut,len(steps)))
                for i in range(copies) for j in block]
    rules = {}
    for i,j in schedule:
        _,ins,outs,_ = steps[j]
        rules[i,j] = ([((i+1)%copies if e==edge else i,e) for e in ins],[(i,e) for e in outs])
    return movie(dict(rules=rules),schedule)


def rank_range(data,witness=False,copies=1):
    decorated = marked_net(data,(2,3,4))
    allowed = return_rules(decorated)
    branching = {g for g in allowed if len(g[1])>2}
    if not branching:
        answer = analyze(data,witness)
        return dict(max_component_cycle_rank=int(answer['named_degree_five_obstruction_at_empty_ends']),**answer)
    result = dict(max_component_cycle_rank='unbounded',named_degree_five_obstruction_at_empty_ends=True)
    if witness:
        path = find_return(decorated,allowed,branching)
        drawing = movie(decorated,path)
        chords = max(component_ranks(drawing),key=len)
        assert len(chords)>=2
        expanded = splice_copies(drawing,chords[0],copies)
        ranks = [len(group) for group in component_ranks(expanded)]
        expected = 1+copies*(len(chords)-1)
        assert max(ranks)==expected
        result.update(program=[dict(rule=g,marked_ports=ports) for g,ports in path],
                      movie=drawing,component_chords=chords,spliced_edge=chords[0],
                      spliced_movie=expanded,spliced_component_ranks=ranks)
    return result


def audit():
    from semistrict_surface_spherical_relations import analyze as spheres
    from semistrict_surface_scalar_leaves import prune

    def check(rules,positive,cycle_size=None):
        data = dict(point_gates=sorted({p for ports in rules.values() for side in ports for p in side}),
                    rules={name:(list(a),list(b)) for name,(a,b) in rules.items()})
        result = analyze(data,True)
        assert result['named_degree_five_obstruction_at_empty_ends']==positive
        if positive:
            b = spheres(result['movie'])['betti']
            assert b[1]>0
            if cycle_size:
                assert len(result['cycle'])==cycle_size
        return result

    check({'free':('',''),'birth':('','a'),'split':('a','bc'),'die-b':('b',''),'die-c':('c','')},False)
    # The two marked d-edges close locally, but the s-token must also disappear.
    rules = {'free':('',''),'start':('','sc'),'split':('c','dd'),'close':('dd','')}
    check(rules,False)
    accepted = check(dict(rules,finish=('s','')),True,2)
    assert {accepted['program'][s['event']]['rule'] for s in accepted['cycle']}=={'split','close'}
    # No single birth can feed both ports of a death. The shortest possible
    # marked cycle traverses two births and both deaths, using signed seams.
    square = check({'free':('',''),'birth':('','ab'),'take-a':('aa',''),'take-b':('bb','')},True,4)
    assert any(square['movie']['seams'])
    # Exhaustively compare one-colour one-rule births and deaths with the
    # elementary multigraph criterion (a star if either degree is one).
    for a in range(1,4):
        for b in range(1,4):
            check({'birth':('','a'*a),'death':('a'*b,'')},min(a,b)>=2)
    print('Checked returning forests, a locally closed but stranded bigon, a returned bigon, a four-event cycle and nine arity pairs.')
    for births,deaths,rank in [(1,3,0),(2,2,1),(2,3,'unbounded'),(3,3,'unbounded')]:
        net = dict(point_gates=['a'],rules={'birth':([],['a']*births),'death':(['a']*deaths,[])})
        result = rank_range(net,True,3)
        assert result['max_component_cycle_rank']==rank
        if rank=='unbounded':
            ranks = result['spliced_component_ranks']
            assert max(ranks)>=4 and spheres(result['spliced_movie'])['betti']==[1,sum(ranks),len(ranks)]
    # Arbitrarily many cycles can coexist without a single connected bicycle.
    net = dict(point_gates=['a','leaf'],rules={'birth':([],['a','a','leaf']),
               'death':(['a','a'],[]),'prune':(['leaf'],[])})
    decorated_cycle = rank_range(net,True)
    assert decorated_cycle['max_component_cycle_rank']==1
    reduced = prune(decorated_cycle['movie'])['movie']
    assert [(len(c['input']),len(c['output'])) for c in reduced['charts']]==[(0,2),(2,0)]
    assert spheres(reduced)['betti']==spheres(decorated_cycle['movie'])['betti']
    print('Connected rank bounds and three-copy splices checked on the actual signed spines.')


def typed(directory):
    from catt import STAR,arr,check_ctx,comp2,infer,subst_tm,subst_ty,v
    from emit_agda import Emitter
    from relative_coherence_hidden_seam import identity
    from semistrict_surface_skeletal_base import right_unit

    point = (STAR,)
    u = identity(point,v(0))
    e = identity(point,u)
    scalar = infer(point,e)
    ctx = point+(scalar,scalar)
    a,b = v(1),v(2)
    def port(probe):
        return comp2(ctx,1,comp2(ctx,1,a,probe),b)
    d = port(e)
    ctx += (arr(scalar,e,d),arr(scalar,d,e))
    check_ctx(ctx)
    program = comp2(ctx,2,v(3),v(4))
    chamber = port(program)
    closed = comp2(ctx,2,comp2(ctx,2,v(3),chamber),v(4))
    end = arr(scalar,e,e)
    assert infer(ctx,program)==end and infer(ctx,chamber)==arr(scalar,d,d) and infer(ctx,closed)==end
    if directory:
        emitter = Emitter()
        emitter.check_type('returnAsProbe',ctx,program,end)
        emitter.check_type('probeBesideSelectedGate',ctx,chamber,arr(scalar,d,d))
        emitter.check_type('closedChamberAtWrittenEnds',ctx,closed,end)
        (directory/'CycleReturn.agda').write_text(emitter.module('CycleReturn',__doc__.splitlines()[0]))

    # Fold two cycle colours to h and contract a leaf attached at the birth.
    source = point+(scalar,)*3
    pair = comp2(source,1,v(1),v(2))
    triple = comp2(source,1,pair,v(3))
    source += (arr(scalar,e,triple),arr(scalar,pair,e),arr(scalar,v(3),e))
    check_ctx(source)
    # Consume the right leaf and then the remaining pair at the reduced port.
    leaf = comp2(source,1,pair,v(6))
    step = comp2(source,2,comp2(source,2,v(4),leaf),right_unit(source,pair,2,False))
    closed = comp2(source,2,step,v(5))
    target = point+(scalar,)
    folded = comp2(target,1,v(1),v(1))
    target += (arr(scalar,e,folded),arr(scalar,folded,e))
    check_ctx(target)
    images = [v(0),v(1),v(1),e,comp2(target,2,v(2),right_unit(target,folded,2,True)),
              v(3),identity(target,e)]
    for i,t in enumerate(images):
        assert infer(target,t)==subst_ty(source[i],images[:i])
    projected = subst_tm(closed,images)
    assert infer(source,closed)==end and infer(target,projected)==end
    if directory:
        emitter = Emitter()
        emitter.check_type('returnWithLeaf',source,closed,end)
        emitter.check_type('projectToOneColourAndTwoCapRules',target,projected,end)
        (directory/'UnicyclicReturn.agda').write_text(emitter.module('UnicyclicReturn',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--witness',action='store_true')
    parser.add_argument('--rank-range',action='store_true',help='classify connected cycle ranks as 0, 1, or unbounded')
    parser.add_argument('--copies',type=int,default=1,help='number of copies in a rank-amplification witness')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        result = rank_range(data,args.witness,args.copies) if args.rank_range else analyze(data,args.witness)
        print(json.dumps(result,indent=2))
    else:
        audit()
        typed(args.agda_dir)
