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

from semistrict_surface_empty_returns import find_return, movie, return_rules
from semistrict_surface_scalar_leaves import read_edges


def marked_net(data):
    rules = {}
    for name in return_rules(data):
        inputs,outputs = data['rules'][name]
        ports = inputs+outputs
        for pair in [(),*combinations(range(len(ports)),2)]:
            decorated = [(p,i in pair) for i,p in enumerate(ports)]
            rules[name,pair] = decorated[:len(inputs)],decorated[len(inputs):]
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


def audit():
    from semistrict_surface_spherical_relations import analyze as spheres

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


def typed(directory):
    from catt import STAR,arr,check_ctx,comp2,infer,v
    from emit_agda import Emitter
    from relative_coherence_hidden_seam import identity

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


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--witness',action='store_true')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(analyze(json.loads(args.input.read_text()),args.witness),indent=2))
    else:
        audit()
        typed(args.agda_dir)
