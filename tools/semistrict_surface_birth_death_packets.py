"""Lift compatible paths across a simultaneous proper birth and death.

Use gate-forest JSON fields edges, gates, vertex, path, diagram and a second
joint reading target. The birth and death fields name distinct point markers.
created and consumed are nonempty positioned closed diagrams, with distinct
gate occurrence names throughout. first_path moves the birth marker beside
the consumed diagram. second_path moves the death marker beside the created
diagram. Paths use signed, one-based adjacent exchanges.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, maximal_vars, sub_from, subst_tm, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, steps, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_component_braids import restrict
from semistrict_surface_gate_forests import Presentation, cable
from semistrict_surface_history_group import exchange
from semistrict_surface_shared_edge import braid_image


def follow(diagram, word, ports):
    for step in word:
        if type(step) is not int or not step:
            raise ValueError('expected a nonzero signed exchange')
        diagram = exchange(diagram, step, ports)
        if diagram is None:
            raise ValueError('exchange crosses a wire or lies outside the reading')
    return diagram


def expand(diagram, packets):
    return tuple((pos + local, name) for pos, gate in diagram
                 for local, name in packets.get(gate, ((0, gate),)))


def expand_path(diagram, word, packets):
    return cable(word, [len(packets[gate]) if gate in packets else 1 for _, gate in diagram])


def lift(data, representative=0):
    birth, death = data['birth'], data['death']
    created, consumed = data['created'], data['consumed']
    if birth == death or not created or not consumed:
        raise ValueError('expected two different markers and two nonempty ports')
    model = Presentation(dict(data, rules={'birth': [birth, created], 'death': [death, consumed]}))
    if any(model.ports[g] != ('','') for g in (birth, death)):
        raise ValueError('both markers must have empty spatial boundaries')
    start, target = model.diagram, tuple((p,g) for p,g in data['target'])
    names = [g for _,g in start]
    all_names = names + [g for _,g in list(created) + list(consumed)]
    if len(set(all_names)) != len(all_names) or any(g not in names for g in (birth,death)):
        raise ValueError('expected distinct occurrence names including both markers')
    if sorted(names) != sorted(g for _,g in target):
        raise ValueError('source and target must use the same named occurrences')
    if model.sweep(model.vertex,model.path,target) != model.sweep(model.vertex,model.path,start):
        raise ValueError('joint readings must have parallel boundaries')

    first, second = {death: consumed}, {birth: created}
    x, y = expand(start,first), expand(start,second)
    u, v_path = data['first_path'], data['second_path']
    for chart, word, packet in ((x,u,first),(y,v_path,second)):
        if follow(chart,word,model.ports) != expand(target,packet):
            raise ValueError('path misses its prescribed serial endpoint')
    seam = expand(start, first | second)
    left, right = expand_path(x,u,second), expand_path(y,v_path,first)
    if braid_image(len(seam),left) != braid_image(len(seam),right):
        return None

    packet_names = {g for _,g in consumed}
    selected = consumed[representative][1]
    keep = {i for i,(_,g) in enumerate(x) if g not in packet_names or g == selected}
    joint = restrict(len(x),u,keep)
    if follow(start,joint,model.ports) != target:
        raise AssertionError('the projected path missed the joint chart')
    for chart,word,packet in ((x,u,first),(y,v_path,second)):
        restored = expand_path(start,joint,packet)
        assert braid_image(len(chart),restored) == braid_image(len(chart),word)
    return joint


def audit():
    gates = {g: ['x','',''] for g in ('A','D','s','p','q')}
    for site in ('P','Q','O'):
        gates.update({site+'b':['x','','ab'],site+'d':['x','ab',''],
                      site+'i':['y','','']})
    base = dict(edges={'a':['x','y'],'b':['y','x']},gates=gates,vertex='x',path='',
                birth='A',death='D')
    # A singleton, a disconnected packet and a lens containing an interior point.
    def packets(k):
        lens = [(0,k+'b'),(1,k+'i'),(0,k+'d')]
        point = [(0,k.lower())]
        return (point, lens, lens + point)
    root = ((0,'A'),(0,'s'),(0,'D'))
    checks = incompatible = 0
    for p,q in product(packets('P'),packets('Q')):
        layouts = [(root,0), (((0,'Ob'),(0,'Od')) + root,2)]
        # In the bounded y-face use the reverse pair of edges in local lenses.
        for diagram,offset in layouts + [(((0,'Ob'),(1,'A'),(1,'s'),(1,'D'),(0,'Od')),1)]:
            local = gates
            if offset == 1:
                local = {g: (['y','','ba'] if g in ('Pb','Qb') else
                             ['y','ba',''] if g in ('Pd','Qd') else
                             ['x','',''] if g in ('Pi','Qi') else
                             ['y','',''] if g in ('A','D','s','p','q') else row)
                         for g,row in gates.items()}
            ports = {g:(s,t) for g,(_,s,t) in local.items()}
            def shifted(word):
                return tuple((abs(g)+offset)*(1 if g>0 else -1) for g in word)
            for raw in [(),(1,),(-2,), (1,1), (1,2,1), (1,1,2,2,-1,-1,-2,-2)]:
                joint = shifted(raw)
                target = follow(diagram,joint,ports)
                # Read a different spelling at the second site for the Artin relation.
                other = shifted((2,1,2)) if raw == (1,2,1) else joint
                data = dict(base,gates=local,diagram=diagram,target=target,created=q,consumed=p,
                            first_path=expand_path(diagram,joint,{'D':p}),
                            second_path=expand_path(diagram,other,{'A':q}))
                for i in range(len(p)):
                    got = lift(data,i)
                    assert got is not None and braid_image(len(diagram),got)==braid_image(len(diagram),joint)
                    checks += 1
            # Move just the spectator around the birth site, fixing the other serial path.
            bad = dict(data,target=diagram,first_path=shifted((1,1)),second_path=())
            assert lift(bad) is None
            incompatible += 1
            if len(p)==4:
                # The free p-point circles the whole P lens inside the consumed packet.
                first_chart = expand(diagram,{'D':p})
                i = next(i for i,(_,g) in enumerate(first_chart) if g=='Pb')
                internal = tuple(i+t for t in cable((1,1),[3,1]))
                assert lift(dict(bad,first_path=internal)) is None
                incompatible += 1
    print(f'{checks} compatible path lifts, {incompatible} incompatible pairs rejected')


def audit_intersection():
    # Search the two three-strand groups independently, including paths which
    # split a packet en route. Compare their four-strand intersection with the
    # images of two-strand paths. No joint words generate the serial candidates.
    root = ((0,'A'),(0,'D'))
    p = ((0,'p'),(0,'r'))
    q = ((0,'q'),(0,'s'))
    gates = {g:['x','',''] for g in 'ADprqs'}
    ports = {g:('','') for g in gates}
    base = dict(edges={},gates=gates,vertex='x',path='',birth='A',death='D',
                diagram=root,created=q,consumed=p)
    readings = {}
    bound = 5
    for length in range(bound+1):
        for word in product((-2,-1,1,2),repeat=length):
            if any(a==-b for a,b in zip(word,word[1:])):
                continue
            readings.setdefault(braid_image(3,word),word)
    candidates = matches = 0
    for target in (root,root[::-1]):
        sides = []
        for own,other in (({'D':p},{'A':q}),({'A':q},{'D':p})):
            serial = expand(root,own)
            end = expand(target,own)
            side = {braid_image(4,expand_path(serial,w,other)):w for w in readings.values()
                    if follow(serial,w,ports)==end}
            sides.append(side)
        left,right = sides
        intersection = left.keys() & right.keys()
        expected = set()
        for exponent in range(-(bound//2),bound//2+1):
            w = ((1,) if exponent>0 else (-1,))*abs(exponent)
            if 2*abs(exponent)<=bound and follow(root,w,ports)==target:
                expected.add(braid_image(4,expand_path(root,w,{'D':p,'A':q})))
        assert intersection==expected
        for image in intersection:
            assert lift(dict(base,target=target,first_path=left[image],second_path=right[image])) is not None
        candidates += len(left)*len(right)
        matches += len(intersection)
    print(f'{len(readings)} independent serial braids per side, {candidates} endpoint-compatible pairs, {matches} common seam images')


def typed(directory):
    ctx = (STAR,STAR,arr(STAR,v(0),v(1)),arr(STAR,v(1),v(0)))
    u = identity(ctx,v(0))
    path = comp2(ctx,0,v(2),v(3))
    def between(s,t):
        return arr(infer(ctx,s),s,t)
    ctx += (between(u,path),between(path,u),between(u,u))
    lens = comp2(ctx,1,v(4),v(5))
    consumed = comp2(ctx,1,lens,v(6))
    created = comp2(ctx,1,lens,lens)
    blank = identity(ctx,u)
    ctx += (between(consumed,blank),between(blank,created))
    check_ctx(ctx)
    generic = tree_ctx(string_tree(1,[3,3]))
    slots = maximal_vars(generic)
    paths = [composite(generic,2,steps(generic,list(map(v,slots)),order))
             for order in ((0,1),(1,0))]
    labeling = sub_from(generic,ctx,dict(zip(slots,(v(7),v(8)))))
    track = subst_tm(head(generic,*paths),labeling)
    ends = tuple(subst_tm(t,labeling) for t in paths)
    assert infer(ctx,track) == between(*ends)
    if directory:
        out = Emitter()
        out.check_type('properBirthDeathExchange',ctx,track,between(*ends))
        (directory/'BirthDeathPackets.agda').write_text(out.module('BirthDeathPackets',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps({'joint_path':lift(json.loads(args.input.read_text()))}))
    else:
        audit()
        audit_intersection()
        typed(args.agda_dir)
